package edu.mit.csail.sdg.alloy4whole;

import static edu.mit.csail.sdg.alloy4whole.AmgalgamUI.finalizeProvenances;
import static edu.mit.csail.sdg.alloy4whole.AmgalgamUI.getTestableTuples;
import static edu.mit.csail.sdg.alloy4whole.AmgalgamUI.whyLN;

import java.awt.Color;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javax.swing.JScrollPane;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.WorkerEngine.WorkerCallback;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.CoverageExpansionVisitor;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTraceWrapper;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTree;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import com.microsoft.z3.Context;
import com.microsoft.z3.Optimize;

class BoolVector {
    final List<Boolean> vec;
    
    BoolVector(List<Boolean> vec) {
        this.vec = vec;
    }
     
    public boolean isSubsumedBy(BoolVector o) {
        for (int i = 0; i < vec.size(); i++) {
            if (vec.get(i) && !o.vec.get(i)) {
                return false;
            }
        }
        return true;
    }
    
    public int getNumAugmentedBy(BoolVector o) {
        int cnt = 0;
        for (int i = 0; i < vec.size(); i++) {
            if (!vec.get(i) && o.vec.get(i)) {
                cnt++;
            }
        }
        return cnt;
    }

    public void unify(BoolVector o) {
        for (int i = 0; i < o.vec.size(); i++) {
            if (o.vec.get(i)) vec.set(i, true);
        }
    }
    
    public int count() {
        int cnt = 0;
        for (Boolean b : vec) {
            if (b) cnt++;
        }
        return cnt;
    }

    @Override
    public String toString() {
        return vec.toString();
    }
}

public class CoverageUI {
    final private SwingLogPanel swingLog;
    final private CoverageTextLog textLog;
    public Module root;
    private WorkerCallback out;
    static CoverageTimeLogger timeLogger = new CoverageTimeLogger();
    List<ProvenanceTraceWrapper> accumTraces;
    Set<ProvenanceTraceWrapper> accumTracesSet;

    public CoverageUI(Module root, SwingLogPanel swingLog, CoverageTextLog textLog, WorkerCallback out) {
        /*
         * swingLog must not be null
         */
        this.root = root;
        
        if (swingLog == null) {
            JScrollPane logpane = OurUtil.scrollpane(null);
            this.swingLog = new SwingLogPanel(logpane, "Lucida Grande", 0, Color.BLACK, Color.BLACK, Color.BLACK, null);
        } else {
            this.swingLog = swingLog;
        }
        
        this.textLog = textLog;
        this.out = out;
    }
    

    public List<Integer> getCoverage(A4Solution ans, boolean b, HashMap<ExprVar, List<ExprVar>> eq_classes) throws Err {
        // TODO Test only sigs that are atomic (right now, catching exception below)
        //      For instance, remainder sigs won't be tested.
        Set<AmalgamTupleInExpr> toTest = getTestableTuplesReduced(root, ans, b, eq_classes);
        String testName = Util.asList("+", "-").get(b ? 0 : 1);
        List<Integer> traces = new ArrayList<>();
        CoverageExpansionVisitor expander = new CoverageExpansionVisitor(root, ans);
        
        // Could not use TimeLogger since we want to *accumulate* time spent over many literals.
        // Note that microbenchmarking like this is iffy, partly because of GC.
        long msTime;
        long msAmalgam = 0;
        long msCovExpansion = 0;
        
        for(AmalgamTupleInExpr test : toTest) {
            msTime = System.currentTimeMillis();
            whyLN(swingLog, root, ans, testName, test);
            finalizeProvenances();
            msAmalgam += (System.currentTimeMillis() - msTime);
            
            msTime = System.currentTimeMillis();
            for(ProvenanceTree p : AmgalgamUI.provenanceTrees) {
                ProvenanceTraceWrapper trace = new ProvenanceTraceWrapper(p.trace(), expander, b);
                //System.out.println("trace: " + trace);
                //System.out.println("otrace: " + trace.getTrace());
                if (accumTracesSet.contains(trace)) {
                    traces.add(accumTraces.indexOf(trace));
                } else {
                    boolean willAdd = true;
                    for (int i = 0; i < accumTraces.size(); i++) {
                        ProvenanceTraceWrapper o = accumTraces.get(i);
                        if (o == null) continue;
                        boolean tSo = trace.isSubsumedBy(o);
                        boolean oSt = o.isSubsumedBy(trace);
                        if (tSo && oSt) {
                            willAdd = false;
                            traces.add(i);
                            break;
                        } else if (tSo) {
                            willAdd = false;
                            break; 
                        } 
                        /*
                        if (o.isSubsumedBy(trace)) {
                            accumTracesSet.remove(o);
                            accumTraces.set(i, null);
                        }
                        */
                    }
                    if (willAdd) {
                        accumTracesSet.add(trace);
                        accumTraces.add(trace);
                        traces.add(accumTraces.size() - 1);
                        //System.out.println(SkeletonPrettifier.prettify(trace));
                    }
                }
            }
            msCovExpansion += (System.currentTimeMillis() - msTime);
        }
        
        final boolean printTime = true;
        if(printTime) {
            log("  Time spent in Amalgam scan: "+msAmalgam+" ms; Coverage Expansion: "+msCovExpansion+" ms.\n");
        }
        
        return traces;
    }

    public static HashMap<ExprVar, List<ExprVar>> getAtomEqClass(Module root, A4Solution ans, boolean b) {
        HashMap<ExprVar, List<ExprVar>> eq_class = new HashMap<>();
        
        /*
        HashMap<String, ExprVar> map = new HashMap<>();
        for (ExprVar atom : ans.getAllAtoms()) {
            map.put(atom.toString(), atom);
        }
        
        Bounds bounds = ans.getBounds();
        for (Sig s: root.getAllReachableSigs()) {
            // filter out field stuff

            if (s.equals(Sig.UNIV) || s.equals(Sig.NONE) || s.equals(Sig.STRING) ||
                    s.equals(Sig.SEQIDX) || s.equals(Sig.SIGINT)) {
                continue;
            }
            if (s.toString().startsWith("Ord/")) continue;
            if (s.hasChildren()) continue;
            Expression sigR = ans.a2k().get(s); // kodkod expression corresponding to this sig
            if(!(sigR instanceof Relation)) {
                // result.append("Skipping non-relation sig: "+sigR+"\n");
                continue;
            }
            TupleSet ts = bounds.upperBound((Relation)sigR);
            List<Tuple> tups = Util.copyIterator(ts.iterator());
            if (tups.isEmpty()) {
                continue;
            }
            List<ExprVar> tupsOut = new ArrayList<>(tups.size());
            for (Tuple t : tups) {
                tupsOut.add(map.get(ans.atom2name.get(t.atom(0).toString())));
            }
            eq_class.put(map.get(ans.atom2name.get(tups.get(0).atom(0).toString())), tupsOut);
        }
        */


        Set<AmalgamTupleInExpr> model = getTestableTuples(root, ans, b);
        Iterable<ExprVar> atoms = ans.getAllAtoms();
        HashMap<ExprVar, List<AmalgamTupleInExpr>> assoc = new HashMap<>();
        HashMap<ExprVar, Object> atom_object = new HashMap<>();
        for (ExprVar atom : atoms) {
            List<AmalgamTupleInExpr> lst = new ArrayList<>();
            String atomStr = atom.toString();
            for (AmalgamTupleInExpr assign : model) {
                int arity = assign.t.arity();
                boolean found = false;
                for (int i = 0; i < arity; i++) {
                    if (assign.t.atom(i).equals(atomStr)) {
                        atom_object.put(atom, assign.t.getOriginalTuple().atom(i));
                        found = true;
                        break;
                    }
                }
                if (found) {
                    lst.add(assign);
                }
            }
            assoc.put(atom, lst);
        }

        List<ExprVar> atom_list = new ArrayList<>();
        for (ExprVar atom : atoms) {
            if (b && atom.toString().startsWith("unused")) continue;
            if (!b && !atom.toString().startsWith("unused")) continue;
            atom_list.add(atom);
            List<ExprVar> lst = new ArrayList<>();
            lst.add(atom);
            eq_class.put(atom, lst);
        }

        HashSet<ExprVar> visited = new HashSet<>();

        for (int i = 0; i < atom_list.size(); i++) {
            ExprVar ai = atom_list.get(i);
            if (visited.contains(ai)) continue;

            for (int j = i + 1; j < atom_list.size(); j++) {
                ExprVar aj = atom_list.get(j);
                if (visited.contains(aj)) continue;

                String ai_str = ai.toString();
                String aj_str = aj.toString();

                // is aj isomorphic to ai?
                List<AmalgamTupleInExpr> assoc_i = assoc.get(ai);
                List<AmalgamTupleInExpr> assoc_j = assoc.get(aj);
                if (assoc_i.size() != assoc_j.size()) continue;

                if (assoc_i.isEmpty()) {
                    visited.add(aj);
                    eq_class.get(ai).add(aj);
                    eq_class.remove(aj);
                    continue;
                }

                List<AmalgamTupleInExpr> new_assoc_j = new ArrayList<>();

                for (AmalgamTupleInExpr assign : assoc_j) {
                    Tuple old_tuple = assign.t.getOriginalTuple();
                    TupleFactory factory = old_tuple.universe().factory();


                    List<Object> lst = new ArrayList<>();
                    int arity = old_tuple.arity();
                    for (int k = 0; k < arity; k++) {
                        Object atom = old_tuple.atom(k);
                        String atom_str = ans.atom2name.get(atom.toString());
                        if (atom_str.equals(aj_str)) {
                            lst.add(atom_object.get(ai));
                        } else if (atom_str.equals(ai_str)) {
                            lst.add(atom_object.get(aj));
                        } else {
                            lst.add(atom);
                        }
                    }
                    new_assoc_j.add(new AmalgamTupleInExpr(
                            assign.e,
                            new A4Tuple(factory.tuple(lst), ans),
                            false,
                            b));
                }

                HashSet<String> new_assoc_j_str = new HashSet<>();
                HashSet<String> assoc_i_str = new HashSet<>();

                for (AmalgamTupleInExpr e : new_assoc_j) new_assoc_j_str.add(e.toString());
                for (AmalgamTupleInExpr e : assoc_i) assoc_i_str.add(e.toString());

                if (new_assoc_j_str.equals(assoc_i_str)) {
                    visited.add(aj);
                    eq_class.get(ai).add(aj);
                    eq_class.remove(aj);
                    continue;
                }
            }
        }
        return eq_class;
    }

    public Set<AmalgamTupleInExpr> getTestableTuplesReduced(
            Module root, A4Solution ans, boolean b, HashMap<ExprVar, List<ExprVar>> eq_classes) {
        Set<AmalgamTupleInExpr> toTest = getTestableTuples(root, ans, b);
        //log("Equivalence classes: " + eq_classes.toString() + "\n");

        Set<AmalgamTupleInExpr> ret = new HashSet<>();
        for (AmalgamTupleInExpr asgn : toTest) {

            String asgnStr = asgn.toString();
            boolean will_add = true;
            for (List<ExprVar> eq_class : eq_classes.values()) {
                 // State
                 // -1: will not add
                 // 0: still see consecutive atoms
                 // 1: see consecutive atoms and it discontinues.
                int state = 0;
                for (ExprVar atom : eq_class) {
                    if (asgnStr.contains(atom.toString())) {
                        if (state == 1) {
                            state = -1;
                            break;
                        }
                    } else {
                        if (state == 0) {
                            state = 1;
                        }
                    }
                }
                if (state == -1) {
                    //log("Literal " + asgn.toString() + " is eliminated\n");
                    will_add = false;
                    break;
                }
            }
            if (will_add) {
                //log("Literal " + asgn.toString() + " is kept\n");
                ret.add(asgn);
            }
        }
        return ret;
    }

    public void log(String s) {
        swingLog.log(s);
        if (out != null) {
            Object[] arr = {"debug", s};
            out.callback(arr);
        }
        if (textLog != null) textLog.log(s);
    }
    
    public CoverageStruct fromInitialSol(
            A4Solution sol, 
            CoverageOptions coptions) throws Err, IOException {
        Runtime runtime = Runtime.getRuntime();
        runtime.gc();
        long memoryInitial = (runtime.totalMemory() - runtime.freeMemory()) / 1000000;
        long limitMemory = memoryInitial + 4000;
        System.out.println("limit-memory: " + limitMemory);
        
        List<CoverageModel> models = new ArrayList<>();
        
        accumTraces = new ArrayList<>();
        accumTracesSet = new HashSet<>();
        
        Context ctx = new Context();
        Optimize solver = ctx.mkOptimize();
        
        String mode = "diff";
        if (coptions.satTrick) {
            mode = "coverage";
        }
        if (!coptions.inclusive) {
            sol = sol.next(mode);
        }
        long startTime = System.currentTimeMillis();
        timeLogger.pushTime();
        boolean gcHit = false;
        int trial = -1;
        for (
                trial = 1;
                sol.satisfiable() 
                && (coptions.timeLimit == -1 || (System.currentTimeMillis() - startTime) <= coptions.timeLimit)
                && (coptions.modelLimit == -1 || trial <= coptions.modelLimit);
                trial++) {
            if (trial < 0) {
                sol = sol.next(mode);
                continue;
            }
            log("i = " + trial + "\n");
            timeLogger.pushTime();
            CoverageModel m = new CoverageModel(sol, this, ctx, trial);
            timeLogger.popTime("computing coverage");
           
            
            boolean toAdd = true;
            if (!m.isPrincipal) {
                for (int i = 0; i < models.size(); i++) {
                    CoverageModel o = models.get(i);
                    if (o == null) continue;
                    if (m.size >= o.size && m.isSubsumedBy(o)) {
                        toAdd = false;
                        break;
                    }
                    if (!o.isPrincipal && o.size >= m.size && o.isSubsumedBy(m)) {
                        models.set(i, null);
                    }
                }
            }
            
            if (toAdd) models.add(m);
            m.accumNumTrace = accumTracesSet.size();
            log("Prov: " + m.setTraces.size() + ", Prov accum: " + accumTracesSet.size() + "\n");
            sol = sol.next(mode);
            m.timeSoFar = (System.currentTimeMillis() - startTime) / 1000;
            log("Time spent so far: " + m.timeSoFar + " s\n");
            long memory = (runtime.totalMemory() - runtime.freeMemory()) / 1000000;
            System.out.println("Used memory is mbbytes: " + memory);
            if (memory >= limitMemory) {
                gcHit = true;
                runtime.gc();
            }
            memory = (runtime.totalMemory() - runtime.freeMemory()) / 1000000;
            if (memory >= limitMemory) break;
        }
        
        
        long timeAll = (System.currentTimeMillis() - startTime) / 1000;;
        boolean isFinishedEnum = false;
        
        if (!sol.satisfiable()) isFinishedEnum = true;
        
        List<CoverageModel> compactedModels = new ArrayList<>(models.size());
        for (CoverageModel m : models) {
            if (m != null) compactedModels.add(m);
        }
        
        timeLogger.popTime("enumerating sols");

        CoverageStruct ret = new CoverageStruct(this, ctx, solver, accumTraces, accumTracesSet, isFinishedEnum, compactedModels, trial - 1, timeAll, gcHit);
        
        accumTracesSet = null;
        accumTraces = null;
        
        return ret;
    }

    public List<ProvenanceTraceWrapper> justFind(A4Solution sol, CoverageOptions coptions) throws Err {
        List<ProvenanceTraceWrapper> all = new ArrayList<>();
        String mode = "diff";
        if (coptions.satTrick) {
            mode = "coverage";
        }
        for (
                int trial = 1;
                sol.satisfiable() 
                && (coptions.modelLimit == -1 || trial <= coptions.modelLimit);
                trial++) {
            if (trial < 0) {
                sol = sol.next(mode);
                continue;
            }
            log("i = " + trial + "\n");
            
            HashMap<ExprVar, List<ExprVar>> eq_classes = getAtomEqClass(root, sol, true);
            eq_classes.putAll(getAtomEqClass(root, sol, false));

            for (int j = 0; j < 2; j++) {
                Set<AmalgamTupleInExpr> toTest = getTestableTuplesReduced(root, sol, j == 0, eq_classes);
                String testName = Util.asList("+", "-").get(j);
                //List<Integer> traces = new ArrayList<>();
                CoverageExpansionVisitor expander = new CoverageExpansionVisitor(root, sol);
                
                //                 
                for(AmalgamTupleInExpr test : toTest) {
                    whyLN(swingLog, root, sol, testName, test);
                    finalizeProvenances();
                    
                    for(ProvenanceTree p : AmgalgamUI.provenanceTrees) {
                        ProvenanceTraceWrapper trace = new ProvenanceTraceWrapper(p.trace(), expander, j == 0);
                        if (all.contains(trace)) {
                            continue;
                        }
                        all.add(trace);
                    }
                }
            }
            sol = sol.next(mode);
        }
        return all;
    }
    
    public static void printAllProv(List<ProvenanceTraceWrapper> traces) {
        int counter = 1;
        for (ProvenanceTraceWrapper t : traces) {
            System.out.println(counter + "===================");
            System.out.println((t.getSign() ? "why" : "why not")+" "+t.getTrace());
            System.out.println("-------------------");
            System.out.println(CoverageSkeletonPrettifier.prettify(t));
            System.out.println("===================");
            counter++;
        }
    }
}
