package edu.mit.csail.sdg.alloy4whole;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4SolutionReader;
import edu.mit.csail.sdg.alloy4compiler.translator.AmalgamNaiveEvaluator;
import edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper;

public class CoverageModel {
    public final A4Solution ansI;
    //public final A4Solution ans;
    public Set<Integer> setTraces;
    BoolVector bitvec;
    public final BoolExpr modelSym;
    public final IntExpr costSym;
    final Context ctx;
    public final int id;
    public final int size;
    public boolean isDisabled = false;
    
    static int gensym = 0;
    
    public final long computedTime;
    public int accumNumTrace;
    public long timeSoFar;
    public int queueProvCoverage;
    public boolean isPrincipal;
    
    static String gensym() {
        gensym++;
        return "" + gensym;
    }
    
    CoverageModel(A4Solution ansI, CoverageUI coverageEngine, Context ctx, int id) throws Err, IOException {
        this.id = id;
        this.ansI = ansI;
        //this.ansI = null;
        
        Random r = new Random();
        String tempDir = System.getProperty("java.io.tmpdir");
        
        String filenameXML = tempDir+File.separator+"amalgam-coverage" + r.nextInt(); 
        ansI.writeXML(filenameXML);
        A4Solution ans = A4SolutionReader.read(ansI.getAllReachableSigs(), new XMLNode(new File(filenameXML)));
        //this.ans = ans;
        (new File(filenameXML)).delete();
        
        HashMap<ExprVar, List<ExprVar>> eq_classes = CoverageUI.getAtomEqClass(coverageEngine.root, ans, true);
        eq_classes.putAll(CoverageUI.getAtomEqClass(coverageEngine.root, ans, false));
        
        this.ctx = ctx;
        long startTime = System.currentTimeMillis();
        int lastAccumSize = coverageEngine.accumTraces.size();
        this.setTraces = new HashSet<>();
        this.setTraces.addAll(coverageEngine.getCoverage(ans, true, eq_classes));
        this.setTraces.addAll(coverageEngine.getCoverage(ans, false, eq_classes));
        
        AmalgamNaiveEvaluator.storedCaches.remove(ans);        
        AmalgamVisitorHelper.clearExprCache();
        AmalgamVisitorHelper.clearResolvedCache();
        
        this.isPrincipal = (lastAccumSize != coverageEngine.accumTraces.size());
        this.computedTime = System.currentTimeMillis() - startTime;
        this.bitvec = null;
        this.modelSym = ctx.mkBoolConst("b" + gensym());
        this.costSym = ctx.mkIntConst("c" + gensym());
        this.size = ansI.eval(Sig.UNIV).size();
        //compactSetTrace(coverageEngine.accumTraces);
    }
    
    /*
    public void compactSetTrace(List<ProvenanceTraceWrapper> accumTraces) {
        Set<Integer> ret = new HashSet<>(setTraces.size());
        for (Integer x : setTraces) {
            if (accumTraces.get(x) != null) {
                ret.add(x);
            }
        }
        setTraces = ret;
    }
    */
    
    public BoolVector computeBitvec(int size) {
        List<Boolean> vec = new ArrayList<>(Collections.nCopies(size, false));
        for (Integer idx : setTraces) {
            vec.set(idx, true);
        }
        bitvec = new BoolVector(vec);
        return bitvec;
    }
    
    public BoolVector getBitvec() {
        return bitvec;
    }
    
    public BoolExpr getConstraint() {
        int univSize = size;
        univSize = univSize * univSize;
        univSize += 1000;
        // minimize \sum_M univSize(M)^2
        // so that a model of size 3, 3 is more preferable to a model of size 1, 5
        return ctx.mkAnd(
                ctx.mkImplies(modelSym, ctx.mkEq(costSym, ctx.mkInt(univSize))),
                ctx.mkImplies(ctx.mkNot(modelSym), ctx.mkEq(costSym, ctx.mkInt(0))));
    }
    
    public boolean isSubsumedBy(CoverageModel o) {
        return o.setTraces.containsAll(setTraces);
    }
}