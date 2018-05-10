package edu.mit.csail.sdg.alloy4whole;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.swing.JComboBox;

import edu.mit.csail.sdg.alloy4.A4Preferences;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.OurDialog;
import edu.mit.csail.sdg.alloy4compiler.ast.Browsable;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.AmalgamEvalVisitor;
import edu.mit.csail.sdg.alloy4compiler.translator.AmalgamNaiveEvaluator;
import edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper;
import edu.mit.csail.sdg.alloy4compiler.translator.Provenance;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceNode;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTree;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import kodkod.ast.BinaryExpression;
import kodkod.ast.Expression;
import kodkod.ast.Relation;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

public class AmgalgamUI {

    static Module root;
    static A4Solution ans;
    static String lastPrefix;
    static AmalgamTupleInExpr test;
    static A4Solution flipped;
    static Map<Expr, ProvenanceTree> treesForTopLevel = new HashMap<Expr, ProvenanceTree>();
    public static List<ProvenanceTree> provenanceTrees = new ArrayList<ProvenanceTree>();
    public static List<ProvenanceTree> literalProvenanceTrees = new ArrayList<ProvenanceTree>();

    /** Record the green/red nodes of the provenance trace. That is, the instantiated portions
     *  of the spec that can be deduced based on the rest of M.
     *
     *  At the moment, cleared out every time we call whyLN. */
    static Set<Expr> diffExprsVisited = new HashSet<Expr>();

    public static String getLastTestString() {
        if(test!=null) return test.toString(); else return "";
    }

    public static String whyLN(SwingLogPanel log, Module newroot, A4Solution newans, String prefix, AmalgamTupleInExpr testtup) throws Err {
        root = newroot;
        ans = newans;
        lastPrefix = prefix;
        test = testtup;
        treesForTopLevel.clear();
        StringBuilder result = new StringBuilder();
        long currentms = System.currentTimeMillis();

        diffExprsVisited.clear();

        if(test == null) {
            return "";
        }
        flipped = new A4Solution(ans, test);
        //System.out.println("DEBUG: flipped a2k equal? "+flipped.a2k().equals(ans.a2k()));

        List<Expr> sigConstraints = TranslateAlloyToKodkod.rebuildNonFactFormulas(root, log, ans);
        Expr cmdFmla = findCurrentCommand(root, ans);
        Set<Expr> allFacts = new HashSet<Expr>();
        // ** getAllReachableFacts returns:
        //   "the conjunction of all facts in this module and all reachable submodules
        //     (not including field constraints, nor including sig appended constraints)"
        for(Browsable subFact : root.getAllReachableFacts().getSubnodes()) {
            if(!(subFact instanceof Expr)) throw new ErrorFatal("!!! Amalgam Evaluator unexpected subexpression was not an Expr: "+subFact);
            allFacts.add((Expr)subFact);
        }

        // sigConstraints + cmdFmla + allFacts = set of possible root fmlas violated
        // Build all possible subfmlas

        // Assemble overall formula that becomes false:
        List<Expr> fmlas = new ArrayList<Expr>();
        fmlas.add(cmdFmla);
        for(Expr sigC : sigConstraints) fmlas.add(sigC);
        for(Expr fct : allFacts) fmlas.add(fct);

        AmalgamVisitorHelper.removeDuplicateConstraints(fmlas);

        /* result.append("--- Bounds (via ans.getBounds()) ---\n");
        result.append(ans.getBounds());
        result.append("--- Bounds (via flipped.getBounds()) ---\n");
        result.append(flipped.getBounds());
         */

        // Get all provenance trees
        for(Expr f : fmlas) {
            Object flipeval = null;
            flipeval = flipped.eval(f);
            if(Boolean.FALSE.equals(flipeval)) {
                // Note new visitor for each top level; will miss differing exprs
                result.append("----------------------------------------\n");
                result.append("Violated top-level fmla: "+f+"\n");
                //result.append("Removing that literal fails top level constraint: "+f+"\n");
                AmalgamEvalVisitor v = new AmalgamEvalVisitor(root, ans, flipped, test.e, test.t);
                //System.err.println("For f="+f+"; got result "+flipeval);
                // Mandate the top-level formula that fails is the root of the tree, without allowing simplifying it out
                ProvenanceTree t = f.accept(v).disallowCollapse();
                t = ProvenanceNode.construct(ProvenanceNode.Op.PAND, f, true, Collections.singletonList(t)).disallowCollapse();
                diffExprsVisited.addAll(v.getDifferentExprsVisited());

                result.append("Statistics: expressions differenced: "+v.diffCache.size()+"; num visits: "+v.numSanityChecks+"\n");
                //System.err.println(t); // DEBUG
                treesForTopLevel.put(f, t.simplify());
            }
        }
        // Uncomment to show the graph explicitly.
        //t.buildDisplay(null).display()
        result.insert(0,"\n====================================\n");
        result.insert(0,"Building all provenance trees took: "+(System.currentTimeMillis()-currentms)+" ms.\n");
        result.insert(0, "...is necessary.\n");
        result.insert(0, prefix+test+"\n");
        result.insert(0,"Explaining why...\n");
        result.append("----------------------------------------\n");
        result.append("====================================\n");

        // Remove the flipped model from the evaluation cache
        AmalgamNaiveEvaluator.storedCaches.remove(flipped);

        return result.toString();
    }

    // top level trees -> Provenance trees (trees with only AND nodes) -> Provenances (traces of failing formulas justified by alphas)
    public static String finalizeProvenances() throws Err {
        provenanceTrees.clear();
        literalProvenanceTrees.clear();
        StringBuilder result = new StringBuilder();
        // top level trees -> Provenance trees (trees with only AND nodes)
        for(Expr f : treesForTopLevel.keySet()) {
            ProvenanceTree t = treesForTopLevel.get(f).simplify();
            provenanceTrees.addAll(t.orsplit());
        }
        result.append("\nGot "+provenanceTrees.size()+" provenances in total.\n");
        if(!provenanceTrees.isEmpty()) result.append("Use @prov [0..."+(provenanceTrees.size()-1)+"] to view each provenance.");
        if(!provenanceTrees.isEmpty()) result.append("Use @lprov [0..."+(provenanceTrees.size()-1)+"] to view a literal provenance for each.");

        // Also record a literal provenance for each provenance
        if(A4Preferences.LiteralProv.get() > 0) {
            for(ProvenanceTree t : provenanceTrees) {
                //  TODO doesn't handle case where split branches being taken
                literalProvenanceTrees.add(t.expandAntecedents(root, ans, flipped));
            }
        }
        return result.toString();
    }

    public static void doLNTesting(SwingLogPanel log, Module root, A4Solution ans, AmalgamTupleInExpr test, StringBuilder result, boolean sayLUN, String prefix) throws Err {
        try {
            A4Solution flipped = new A4Solution(ans, test);

            // Check reachable facts
            Object evalResultFacts = flipped.eval(root.getAllReachableFacts());
            if(!(evalResultFacts instanceof Boolean))
                throw new ErrorFatal("Amalgam: eval result not boolean: "+evalResultFacts);
            boolean necessaryFromFacts = (Boolean) evalResultFacts != true;

            Expr cmdFmla = findCurrentCommand(root, ans);

            // Check current command
            boolean necessaryFromCommand = false;
            if(cmdFmla != null) {
                Object evalResultCmd = flipped.eval(cmdFmla);
                if(!(evalResultCmd instanceof Boolean))
                    throw new ErrorFatal("Amalgam: eval result not boolean: "+evalResultCmd);
                necessaryFromCommand = ! (Boolean) evalResultCmd;   // evaluate to false -> necessary
            }

            // Check sig constraints
            List<Expr> sigConstraints = TranslateAlloyToKodkod.rebuildNonFactFormulas(root, log, ans);
            boolean necessaryFromSigs = false;
            for(Expr sc : sigConstraints) {
                Object evalResultSC = flipped.eval(sc);
                if(!(evalResultSC instanceof Boolean))
                    throw new ErrorFatal("Amalgam: eval result not boolean: "+evalResultSC);
                necessaryFromSigs |= !((Boolean) evalResultSC);
            }

            // TODO Currently lacking some constraints from BoundsComputer

            // Check overall necessity
            if(necessaryFromFacts || necessaryFromCommand || necessaryFromSigs)
                result.append("[LN] "+prefix+test +" is locally necessary.\n");
            else if(sayLUN)
                result.append("[LU] "+prefix+test + " is NOT locally necessary.\n");
        } catch(ErrorFatal e) {
            result.append("Could not check "+test+"\n");
        }

    }

    // Note that a subexpr might differ even if a higher subexpression doesn't.
    // Trivial example: x in R iff x in R (tautologous). Testing R(1)

    // Which subexpressions differ?
    /*
        for(Expr sub : v.differingSubExpressions) {
            Object origAnswer = ans.eval(sub);
            Object flipAnswer = flipped.eval(sub);

            // use equalsValue
            if(origAnswer instanceof A4TupleSet && flipAnswer instanceof A4TupleSet) {
                A4TupleSet origTuples = (A4TupleSet) origAnswer;
                A4TupleSet flipTuples = (A4TupleSet) flipAnswer;
                result.append("[tupleset] Subexpr "+sub+" differed: "+origAnswer+"   vs.   "+flipAnswer+"\n");
            }
            else {
                result.append("[bool/int] Subexpr "+sub+" differed: "+origAnswer+"   vs.   "+flipAnswer+"\n");
            }
        }
     */

    public static void prettyPrintExplain(StringBuilder sb, Provenance explain) {
        int counter = 0;
        for(Expr antecedent : explain.alphas) {
            sb.append("ALPHA "+counter+":\n"+antecedent+"\n");
            counter++;
        }
        sb.append("Bindings (for *universal* quantifiers):  { "+explain.bindings+" }\n");
    }

    public static String prettyPrintExplains(Set<Provenance> explains) {
        StringBuilder sb = new StringBuilder();
        sb.append("------------------------\n");
        for(Provenance anExplain : explains) {
            prettyPrintExplain(sb, anExplain);
            sb.append("------------------------\n");
        }
        return sb.toString();
    }

    private static Expr findCurrentCommand(Module root, A4Solution ans) throws Err {
        // Find current command
        Expr cmdFmla = null;
        for(Command c : root.getAllCommands()) {
            //ans.getOriginalCommand();

            // TODO brittle! what if toString doesn't match the text?
            if(c.toString().equals(ans.getOriginalCommand())) {
                cmdFmla = c.formula;
                break;
            }
            // result.append(c+" ("+c.label+";"+c.formula+")\n");
        }
        if(cmdFmla == null)
            throw new ErrorFatal("Failed to find current command object for command string: "+ans.getOriginalCommand());
        return cmdFmla;
    }

    private static class ExprComparator implements Comparator<Expr> {
        public int compare(Expr a, Expr b) {
            return a.toString().compareToIgnoreCase(b.toString());
        }
    }

    public static Set<AmalgamTupleInExpr> getTestableTuples(Module root, A4Solution ans, boolean b) {
        Set<AmalgamTupleInExpr> toTest = new HashSet<AmalgamTupleInExpr>();

        // This won't work; null ptr exception because 2-process separation of solver and UI.
        //Bounds bounds = ans.solver.getBounds();
        // This uses the bounds in the reconstituted A4solution, which we augmented to include the actual upper bounds.
        Bounds bounds = ans.getBounds();

        if(b) {
            for(Sig s: root.getAllReachableSigs()) {
                // subnodes() is syntactic. So it'd include fields, but not subsigs.
                if(!s.equals(Sig.UNIV) && !s.equals(Sig.NONE) && !s.equals(Sig.STRING) &&
                        !s.equals(Sig.SEQIDX) && !s.equals(Sig.SIGINT)) {

                    // TODO Clumsy forbidding of Ord/first, Ord/next etc.
                    if(s.toString().startsWith("Ord/")) continue;

                    // From BoundsComputer: "If sig has children, and sig is not abstract, then create a new relation to act as the remainder."
                    // Abstract sigs cannot be childless (or they will necessarily be empty; nothing to fill the union)
                    if(!s.hasChildren()) {
                        // For each tuple in this relation in the instance, test it
                        for(A4Tuple t : ans.eval(s)) {
                            toTest.add(new AmalgamTupleInExpr(s, t, false, b));
                        }
                    }

                    // Test fields as well (even for abstract sigs).
                    for(Field f : s.getFields()) {   // (getFields gives the field exprs, not getFieldDecls)
                        Expression sigF = ans.a2k().get(f); // kodkod expression corresponding to this field
                        if(!(sigF instanceof Relation) && s.isOne == null) {
                            System.out.println("Skipping non-relation field of non-one sig: "+sigF);
                            continue;
                        }

                        for(A4Tuple t : ans.eval(f)) {
                            // Truncated if non-relation + field of a one sig
                            toTest.add(new AmalgamTupleInExpr(f, t, !(sigF instanceof Relation) && s.isOne != null, b));
                        }
                        /*for(ExprHasName n: d.names) {
                       Field f = (Field)n;
                    }*/
                    }
                }
            }
        } else {
            for(Sig s: root.getAllReachableSigs()) {
                if(!s.equals(Sig.UNIV) && !s.equals(Sig.NONE) && !s.equals(Sig.STRING) &&
                        !s.equals(Sig.SEQIDX) && !s.equals(Sig.SIGINT)) {

                    if(!s.hasChildren()) {
                        Expression sigR = ans.a2k().get(s); // kodkod expression corresponding to this sig
                        if(!(sigR instanceof Relation)) {
                            // result.append("Skipping non-relation sig: "+sigR+"\n");
                            continue;
                        }
                        // For each tuple in this relation's upper bound **NOT** in the instance, test it
                        TupleSet kodkodUpperSig = bounds.upperBound((Relation)sigR);
                        for(Tuple kkt : kodkodUpperSig) {
                            boolean found = false;
                            for(A4Tuple t : ans.eval(s)) {
                                if(t.getOriginalTuple().equals(kkt))
                                {
                                    found = true;
                                    // result.append("(Debug) Not testing: "+t+" in "+s+" because was present in model.\n");
                                    break;
                                }
                            }
                            if(!found) toTest.add(new AmalgamTupleInExpr(s, new A4Tuple(kkt, ans), false, b));
                        }
                    }

                    // Test fields as well.
                    for(Field f : s.getFields()) {
                        Expression sigF = ans.a2k().get(f); // kodkod expression corresponding to this field
                        boolean truncated = false;
                        if(!(sigF instanceof Relation) && s.isOne == null) {
                            System.out.println("SKIPPING non-relation field of non-one sig: "+sigF);
                            continue;
                        } else if (sigF instanceof BinaryExpression) {
                            //System.out.println("Truncating non-relation to produce Kodkod bounds: "+sigF);
                            sigF = ((BinaryExpression)sigF).right();
                            truncated = true;
                        }

                        // For each tuple in this relation's upper bound **NOT** in the instance, test it
                        TupleSet kodkodUpperField = bounds.upperBound((Relation)sigF);
                        for(Tuple kkt : kodkodUpperField) {
                            boolean found = false;
                            for(A4Tuple t : ans.eval(f)) {
                                if(t.getOriginalTuple().equals(kkt))
                                {
                                    found = true;
                                    //result.append("(Debug) Not testing: "+t+" in "+f+" because was present in model.\n");
                                    break;
                                }
                                //result.append("(Debug) Tested tuples: "+t.getOriginalTuple()+" vs. "+kkt+" found :"+t.getOriginalTuple().equals(kkt)+"\n");
                            }
                            if(!found) toTest.add(new AmalgamTupleInExpr(f, new A4Tuple(kkt, ans), truncated, b));
                        }

                    }
                }
            }
        }
        return toTest;
    }


    static AmalgamTupleInExpr getATuple(Module root, A4Solution ans, boolean positiveTuples) throws Err {
        A4Tuple tuple = null;
        Expr relation = null;

        // Build set of options to present to user
        /*Map<Expr, Set<A4Tuple>> inModel = new HashMap<Expr, Set<A4Tuple>>();
        for(Sig s: root.getAllReachableSigs()) {
            // don't include unnecessary, base, sigs
            if(s.equals(Sig.NONE)) continue;
            if(s.equals(Sig.UNIV)) continue;
            if(s.equals(Sig.SIGINT)) continue;
            if(s.equals(Sig.SEQIDX)) continue;
            if(s.equals(Sig.STRING)) continue;

            if(!inModel.containsKey(s))
                inModel.put(s, new HashSet<A4Tuple>());

            // For each tuple in this relation in the instance, test it
            for(A4Tuple t : ans.eval(s)) {
                inModel.get(s).add(t);
            }

            // Test fields as well. (getFields gives the field exprs, not getFieldDecls)
            for(Field f : s.getFields()) {
                if(!inModel.containsKey(f))
                    inModel.put(f, new HashSet<A4Tuple>());

                for(A4Tuple t : ans.eval(f)) {
                    inModel.get(f).add(t);
                } // XXX some dupe code with evaluator; check for missing code here if we change that
            }
        }
         */
        // If this is a whynot, instead subtract possibilities from bounds
        Map<Expr, Set<A4Tuple>> possibilities = new HashMap<Expr, Set<A4Tuple>>();
        Set<AmalgamTupleInExpr> testable = getTestableTuples(root, ans, positiveTuples);
        for(AmalgamTupleInExpr te : testable) {
            if(!possibilities.containsKey(te.e))
                possibilities.put(te.e, new HashSet<A4Tuple>());
            possibilities.get(te.e).add(te.t);
        }

        // get relation
        JComboBox<Expr> dropdownR = new JComboBox<Expr>();
        List<Expr> relList = new ArrayList<Expr>(possibilities.keySet());
        relList.sort(new ExprComparator());
        for(Expr r : relList) {
            dropdownR.addItem(r);
        }

        if(!OurDialog.getInput("Explain which sig/field?", dropdownR)) return null;
        relation = (Expr) dropdownR.getSelectedItem();
        if(relation == null) {
            throw new ErrorFatal("Choice invalid: "+relation);
        }

        // get tuple
        JComboBox<A4Tuple> dropdownT = new JComboBox<A4Tuple>();
        for(A4Tuple t : possibilities.get(relation)) {
            dropdownT.addItem(t);
        }
        // convert the alloy tuple selection to a kodkod one
        if(!OurDialog.getInput("Which "+relation+"?", dropdownT)) return null;

        tuple = (A4Tuple) dropdownT.getSelectedItem();
        if(tuple == null) {
            throw new ErrorFatal("Tuple choice invalid");
        }

        boolean isOneTruncated = false;
        if(relation instanceof Field) {
            Field rf = (Field) relation;
            Expression kodkodExpr = ans.a2k().get(rf);
            if (rf.sig.isOne != null && !(kodkodExpr instanceof Relation))
                isOneTruncated = true;
        }

        return new AmalgamTupleInExpr(relation, tuple, isOneTruncated, positiveTuples);
    }

}
