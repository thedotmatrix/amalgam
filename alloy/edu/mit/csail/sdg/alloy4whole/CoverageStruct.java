package edu.mit.csail.sdg.alloy4whole;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Optimize;
import com.microsoft.z3.Status;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTraceWrapper;

public class CoverageStruct {
    final public CoverageUI coverage;
    final public Context ctx;
    final public Optimize solver;
    public List<ProvenanceTraceWrapper> accumTraces;
    final public boolean isFinishedEnum;
    final public List<CoverageModel> models;
    public Set<ProvenanceTraceWrapper> accumTracesSet;
    final public int numAllModels;
    final public long timeAll;
    final public boolean gcHit;

    public CoverageStruct(CoverageUI coverage, Context ctx, Optimize solver, 
            List<ProvenanceTraceWrapper> accumTraces, Set<ProvenanceTraceWrapper> accumTracesSet, 
            boolean isFinishedEnum, List<CoverageModel> models, int numAllModels, long timeAll, boolean gcHit) {
        this.coverage = coverage;
        this.ctx = ctx;
        this.solver = solver;
        this.accumTraces = accumTraces;
        this.accumTracesSet = accumTracesSet;
        this.isFinishedEnum = isFinishedEnum;
        this.models = models;
        this.numAllModels = numAllModels;
        this.timeAll = timeAll;
        this.gcHit = gcHit;
    }
    
    public int getMissing(List<ProvenanceTraceWrapper> other) {
        Set<ProvenanceTraceWrapper> accumTracesSet = new HashSet<>(this.accumTracesSet);
        List<ProvenanceTraceWrapper> accumTraces = new ArrayList<>(this.accumTraces);
        
        int before = accumTracesSet.size();
        
        for (ProvenanceTraceWrapper trace : other) {
            if (trace == null) continue;
            if (!accumTracesSet.contains(trace)) {
                boolean willAdd = true;
                for (int i = 0; i < accumTraces.size(); i++) {
                    ProvenanceTraceWrapper o = accumTraces.get(i);
                    if (o == null) continue;
                    if (trace.isSubsumedBy(o)) {
                        willAdd = false;
                        break; 
                    }
                }
                if (willAdd) {
                    accumTracesSet.add(trace);
                    accumTraces.add(trace);
                }
            }
        }
        return accumTracesSet.size() - before;
    }
    
    
    public Queue<CoverageModel> getQueue() {
        Set<ProvenanceTraceWrapper> accumTracesSet = new HashSet<>(this.accumTracesSet.size());
        List<ProvenanceTraceWrapper> accumTraces = new ArrayList<>(this.accumTraces.size());
        for (ProvenanceTraceWrapper trace : this.accumTraces) {
            if (trace == null) continue;
            if (!accumTracesSet.contains(trace)) {
                boolean willAdd = true;
                for (int i = 0; i < accumTraces.size(); i++) {
                    ProvenanceTraceWrapper o = accumTraces.get(i);
                    if (o == null) continue;
                    if (trace.isSubsumedBy(o)) {
                        willAdd = false;
                        break; 
                    } 
                    if (o.isSubsumedBy(trace)) {
                        accumTracesSet.remove(o);
                        accumTraces.set(i, null);
                    }
                }
                if (willAdd) {
                    accumTracesSet.add(trace);
                    accumTraces.add(trace);
                }
            }
        }
        
        System.out.println((this.accumTracesSet.size() - accumTracesSet.size()) + " is eliminated for full prov subsumption");
        
        
        List<ProvenanceTraceWrapper> realTraces = new ArrayList<>(accumTraces.size());
        Map<Integer, Integer> mapping = new HashMap<>();
        
        for (int i = 0; i < accumTraces.size(); i++) {
            ProvenanceTraceWrapper trace = accumTraces.get(i);
            if (trace == null) continue;
            realTraces.add(trace);
            mapping.put(i, realTraces.size() - 1);
        }
        
        CoverageUI.printAllProv(realTraces);

        for (CoverageModel m : models) {
            Set<Integer> compactSet = new HashSet<>();
            for (Integer pi : m.setTraces) {
                Integer index = mapping.get(pi);
                if (index != null) compactSet.add(index);
            }
            m.setTraces = compactSet;
        }
        
        this.accumTraces = realTraces;
        this.accumTracesSet = accumTracesSet;
        
        
        // now, don't care about isPrinciple 
        for (int i = 0; i < models.size(); i++) {
            CoverageModel mi = models.get(i); 
            if (mi.isDisabled) continue;
            for (int j = i + 1; j < models.size(); j++) {
                CoverageModel mj = models.get(j);
                if (mj.isDisabled) continue;
                if (mi.size == mj.size) {
                    if (mi.isSubsumedBy(mj)) {
                        mi.isDisabled = true;                        
                    } else if (mj.isSubsumedBy(mi)) {
                        mj.isDisabled = true;
                    }
                } else if (mi.size > mj.size && mi.isSubsumedBy(mj)) {
                    mi.isDisabled = true;
                } else if (mj.size > mi.size && mj.isSubsumedBy(mi)){
                    mj.isDisabled = true;
                }
            }
        }
        
        List<CoverageModel> compactedModels = new ArrayList<>(models.size());
        for (CoverageModel m : models) {
            if (!m.isDisabled) {
                compactedModels.add(m);
            }
        }
        
        coverage.log("Of " + models.size() + " models, only " + compactedModels.size() + " are considered "
                + "as others are subsumed and therefore ignore\n");
        
        for (CoverageModel m : compactedModels) {
            m.computeBitvec(realTraces.size());
            System.out.println(m.id);
            System.out.println(m.getBitvec());
        }
        
        List<IntExpr> costs = new ArrayList<>(compactedModels.size());
        
        for (CoverageModel m : compactedModels) {
            solver.Assert(m.getConstraint()); 
            costs.add(m.costSym);
        }
        
        IntExpr[] arrCosts = new IntExpr[costs.size()];
        for (int t = 0; t < arrCosts.length; t++) {
            arrCosts[t] = costs.get(t);
        }
        solver.MkMinimize(ctx.mkAdd(arrCosts));
        
        for (int i = 0; i < realTraces.size(); i++) {
            List<BoolExpr> disjunction = new ArrayList<>();
            for (CoverageModel m : compactedModels) {
                if (m.getBitvec().vec.get(i)) {
                    disjunction.add(m.modelSym);
                }
            }
            if (!disjunction.isEmpty()) {
                BoolExpr[] arrMods = new BoolExpr[disjunction.size()];
                for (int t = 0; t < arrMods.length; t++) {
                    arrMods[t] = disjunction.get(t);
                }
                solver.Assert(ctx.mkOr(arrMods));                
            }
            
        }
        CoverageUI.timeLogger.pushTime();
        Set<CoverageModel> output = new HashSet<>();
        if (solver.Check() ==  Status.SATISFIABLE) {
            Model modelSAT = solver.getModel();
            for (CoverageModel m : compactedModels) {
                if (modelSAT.eval(m.modelSym, true).equals(ctx.mkTrue())) {
                    output.add(m);
                }
            }
        } else {
            System.out.println("oh no");
        }
        
        List<Boolean> vec = new ArrayList<>(Collections.nCopies(realTraces.size(), false));
        BoolVector acc = new BoolVector(vec);
        List<CoverageModel> queue = new ArrayList<>();
        //Set<ProvenanceTraceWrapper> seen = new HashSet<>();
        
        while (!output.isEmpty()) {
            int maxAugment = 0;
            CoverageModel cmAugment = null;
            for (CoverageModel cm : output) {
                int curr = acc.getNumAugmentedBy(cm.getBitvec());
                if (maxAugment < curr) {
                    maxAugment = curr;
                    cmAugment = cm;
                }
            }
            output.remove(cmAugment);
            queue.add(cmAugment);
            acc.unify(cmAugment.getBitvec());
            cmAugment.queueProvCoverage = acc.count();
        }
        
        CoverageUI.timeLogger.popTime("solving");
        ctx.close();
        return new ArrayDeque<CoverageModel>(queue);
    }
}
