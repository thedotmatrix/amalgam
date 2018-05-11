package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;
import gnu.trove.map.hash.TCustomHashMap;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprITE;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprLet;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprQt;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

/**
 * Experimenting with speed of a naive (i.e., non-Kodkod-invoking) 
 * formula/expression evaluator. That is, we'll lose the benefits
 * of Kodkod's CBC representation, but gain more controllable caching.
 * @author Tim
 *
 */
public class AmalgamNaiveEvaluator extends VisitReturn<Object> {                 
    final A4Solution soln;
    final Module root;   
         
    /** Enable this field to confirm that naive evaluation results match what Kodkod evaluation would return. 
     *  This check is extremely expensive, and should not be used in production. */
    //public final static boolean sanityCheckingExpensive = true;
    public final static boolean sanityCheckingExpensive = false;
    
    // Keep all Expr evaluations for a given instance (i.e., not a weak or soft map)
    // NOTE USING NON-STANDARD HASH MAP IMPLEMENTATION (Trove)    
    // BEWARE using ordinary HashMaps to store Exprs; Exprs use object equality by default
    // If you use an ordinary HashMap in a static field, it will cause a Java "memory leak".
    Map<Expr, Object> singleVisitorCache = new TCustomHashMap<Expr, Object>(AmalgamVisitorHelper.strat, 1000);
           
    public static long cacheHitCountX2 = 0;
    public static long cacheMissCount = 0;
    
    // Let per-instance caches expire as instances go out of scope.
    final public static Map<A4Solution, Map<Expr, Object>> storedCaches = 
            new WeakHashMap<A4Solution, Map<Expr, Object>>();
    
    public AmalgamNaiveEvaluator(Module root, A4Solution soln, boolean storeCache) {     
        //System.out.println("Creating naive evaluator for "+soln.hashCode()+"...");
        this.soln = soln;        
        this.root = root;         
        if(storeCache) {
            // Use whatever's there, if anything
            // If nothing is there, store this new cache
            if(storedCaches.containsKey(soln)) {
                singleVisitorCache = storedCaches.get(soln);
                //System.out.println("Re-using former cache for "+soln.hashCode());
            }
            else
                storedCaches.put(soln, singleVisitorCache);
        }
    }
    
    public void debug(String msg, Expr x) { 
        // See comments in AmalgamEvalVisitor.debug
        if(AmalgamVisitorHelper.debugNEVAL) System.out.println("########## Amalgam NAIVE-EVALUATOR Debug: "+msg+": "+x);
    }
           
    Object lookup(Expr x) { 
        if(singleVisitorCache.containsKey(x)) cacheHitCountX2++;
        else { 
           // System.out.println("Cache miss (soln="+soln.hashCode()+"): "+x+" ("+x.spanIndependentHashCode()+") "+x.span()+"; "+x.getClass());
          /*  if(x instanceof ExprUnary) {
                ExprUnary xu = (ExprUnary) x;
                System.out.println("  unary op was: "+xu.op);
                System.out.println("  sub SI hash wash: "+xu.sub.spanIndependentHashCode()+" class: "+xu.sub.getClass().getSimpleName());
                if(xu.sub instanceof ExprUnary) {
                    ExprUnary xuu = (ExprUnary) xu.sub;
                    System.out.println("    unary op was: "+xuu.op);
                    System.out.println("    sub SI hash was: "+xuu.sub.spanIndependentHashCode()+" class: "+xuu.sub.getClass().getSimpleName());
                    if(xuu.sub instanceof ExprUnary) {
                        ExprUnary xuuu = (ExprUnary) xuu.sub;
                        System.out.println("      unary op was: "+xuuu.op);
                        System.out.println("      sub SI hash was: "+xuuu.sub.spanIndependentHashCode()+" class: "+xuuu.sub.getClass().getSimpleName());
                        
                    }
                    
                }
                
            }*/
            cacheMissCount++;
        }
        return singleVisitorCache.get(x);
    }
    
    Object cacheAndMaybeSanityCheck(Expr x, Object result) throws Err {
        if(sanityCheckingExpensive) {
            Object e = soln.eval(x);
            boolean ok = true;
            if(result instanceof A4TupleSet && e instanceof A4TupleSet) {
                A4TupleSet tsresult = (A4TupleSet) result;
                A4TupleSet eresult = (A4TupleSet) e;
                if(!tsresult.equalValues(eresult)) ok = false;
                if(!ok) {
                    System.err.println("Eval result minus visitor result: "+eresult.minus(tsresult));
                    System.err.println("Visitor result minus eval result:"+tsresult.minus(eresult));
                }
            } else if(result instanceof Boolean && e instanceof Boolean) {
                if(!result.equals(e)) ok = false;
            } else if(result instanceof Integer && e instanceof Integer) {
                if(!result.equals(e)) ok = false;
            } else {    
                ok = false;
            }
            if(!ok) {
                System.err.println("Error context: soln="+soln);
                /*if(e instanceof A4TupleSet) {
                    for(A4Tuple t : (A4TupleSet)e) {
                        System.err.println("Eval tuple: "+t+" ("+t.getOriginalTuple().getClass()+")");
                    }
                }*/                
                throw new ErrorFatal("Sanity check failed on "+x+"\n"+
                             "Visitor returned: "+result+" ("+result.getClass()+")\n"+ 
                             "eval returned:    "+e+" ("+e.getClass()+")");
            }
        }
                
        // Cache
        if(!singleVisitorCache.containsKey(x)) { 
            singleVisitorCache.put(x, result);
        } 
        return result;
    }
    
    public Object handleBinaryRelational(ExprBinary x) throws Err {        
        // It seems like terrible code duplication to set l, r, and result per case.
        // Unfortunately the type of l and r and the arity of result may vary.
        if(x.op.equals(ExprBinary.Op.PLUS)) { 
            A4TupleSet l  = (A4TupleSet) x.left.accept(this);
            A4TupleSet r = (A4TupleSet) x.right.accept(this);            
            A4TupleSet result = new A4TupleSet(l.debugGetKodkodTupleset(), soln);
            return  cacheAndMaybeSanityCheck(x, result.plus(r));
        }
        else if(x.op.equals(ExprBinary.Op.INTERSECT)) { 
            A4TupleSet l  = (A4TupleSet) x.left.accept(this);
            A4TupleSet r = (A4TupleSet) x.right.accept(this);
            A4TupleSet result = new A4TupleSet(l.debugGetKodkodTupleset(), soln);
            return  cacheAndMaybeSanityCheck(x, result.intersect(r));    
        }
        else if(x.op.equals(ExprBinary.Op.MINUS)) { 
            A4TupleSet l  = (A4TupleSet) x.left.accept(this);
            A4TupleSet r = (A4TupleSet) x.right.accept(this);
            A4TupleSet result = new A4TupleSet(l.debugGetKodkodTupleset(), soln);
            return  cacheAndMaybeSanityCheck(x, result.minus(r));    
        }
        else if(x.op.equals(ExprBinary.Op.PLUSPLUS)) {
            A4TupleSet l  = (A4TupleSet) x.left.accept(this);
            A4TupleSet r = (A4TupleSet) x.right.accept(this);
            // Keep everything in left, except what r overrides; add r.  
            // Very similar to PLUS. Note: resolve using first column only per Appendix B of Alloy book.
            
            // What atoms to override?
            Set<Object> overrideAtoms = new HashSet<Object>(); 
            for(A4Tuple t : r) {
                overrideAtoms.add(t.getOriginalTuple().atom(0));
            }
            // Keep what's keepable in l
            TupleSet result = new TupleSet(l.debugGetKodkodTupleset().universe(), l.arity());
            for(A4Tuple t : l) {
                Tuple torig = t.getOriginalTuple();
                if(!overrideAtoms.contains(torig.atom(0))) result.add(torig);
            }            
            
            return  cacheAndMaybeSanityCheck(x, new A4TupleSet(result, soln).plus(r));
        }
        else if(x.op.equals(ExprBinary.Op.DOMAIN)) { 
            A4TupleSet l = (A4TupleSet) x.left.accept(this);
            A4TupleSet r = (A4TupleSet) x.right.accept(this);
            TupleSet result = new TupleSet(l.debugGetKodkodTupleset().universe(), r.arity());
            for(A4Tuple cr : r) {
                for(A4Tuple cl : l) {              
                    // Keep RIGHT if rightmost atom in left matches leftmost in right
                    if(cl.atom(cl.arity()-1).equals(cr.atom(0))) {
                        result.add(cr.getOriginalTuple());
                        break; // found; on to checking next candidate right tuple
                    }
                }
            }
            return cacheAndMaybeSanityCheck(x, new A4TupleSet(result, soln));
        }
        else if(x.op.equals(ExprBinary.Op.RANGE)) {    
            A4TupleSet l = (A4TupleSet) x.left.accept(this);
            A4TupleSet r = (A4TupleSet) x.right.accept(this);
            TupleSet result = new TupleSet(l.debugGetKodkodTupleset().universe(), l.arity());
            for(A4Tuple cl : l) {
                for(A4Tuple cr : r) {                    
                    // Keep LEFT if leftmost atom in right matches rightmost in left.
                    if(cr.atom(0).equals(cl.atom(cl.arity()-1))) {
                        result.add(cl.getOriginalTuple());
                        break; // found; on to checking next candidate right tuple
                    }
                }
            }
            return cacheAndMaybeSanityCheck(x, new A4TupleSet(result, soln));
        }    
        else if(x.op.equals(ExprBinary.Op.ARROW)) { 
            A4TupleSet l  = (A4TupleSet) x.left.accept(this);
            A4TupleSet r = (A4TupleSet) x.right.accept(this);
            A4TupleSet result = l.product(r);            
            return  cacheAndMaybeSanityCheck(x, result);
        }    
        else if(x.op.equals(ExprBinary.Op.JOIN)) {    
            A4TupleSet l  = (A4TupleSet) x.left.accept(this);
            A4TupleSet r = (A4TupleSet) x.right.accept(this);
            TupleSet result = new TupleSet(l.debugGetKodkodTupleset().universe(), l.arity()+r.arity()-2);
            for(A4Tuple lt : l) {                
                for(A4Tuple rt : r) {
                    Tuple newT = AmalgamVisitorHelper.joinTuple(soln, lt, rt);
                    if(newT != null) result.add(newT);
                }
            }
            //debug("    (NEVAL) join: "+x.left+" "+l+" | "+x.right+" "+r+"  => "+result, x);
            return  cacheAndMaybeSanityCheck(x, new A4TupleSet(result, soln));
        }  

        else {
            return err(x);
        }
    }
    
    public Object handleBinaryBoolean(ExprBinary x) throws Err {                
        if(x.op.equals(ExprBinary.Op.AND)) {
            Boolean l = (Boolean) x.left.accept(this);
            if(!l) return  cacheAndMaybeSanityCheck(x, false);
            Boolean r = (Boolean) x.right.accept(this);
            return  cacheAndMaybeSanityCheck(x, l && r);
        } else if(x.op.equals(ExprBinary.Op.OR)) {
            Boolean l = (Boolean) x.left.accept(this);
            if(l) return  cacheAndMaybeSanityCheck(x, true);
            Boolean r = (Boolean) x.right.accept(this);
            return  cacheAndMaybeSanityCheck(x, l || r);
        } else if(x.op.equals(ExprBinary.Op.IMPLIES)) {
            Boolean l = (Boolean) x.left.accept(this);
            if(!l) return  cacheAndMaybeSanityCheck(x, true);
            Boolean r = (Boolean) x.right.accept(this);
            return  cacheAndMaybeSanityCheck(x, !l || r);
        } else if(x.op.equals(ExprBinary.Op.IFF)) {
            Boolean l = (Boolean) x.left.accept(this);
            Boolean r = (Boolean) x.right.accept(this);
            return  cacheAndMaybeSanityCheck(x, (l && r) || (!l && !r));
        } else if(x.op.equals(ExprBinary.Op.IN)) {
            return cacheAndMaybeSanityCheck(x, checkIn(x.left, x.right, true));
        } else if(x.op.equals(ExprBinary.Op.NOT_IN)) {
            return  cacheAndMaybeSanityCheck(x, checkIn(x.left, x.right, false));
        } else if(x.op.equals(ExprBinary.Op.EQUALS)) {
            // XXX Somewhat slower than a direct check, but avoids code reuse
            return checkIn(x.left, x.right, true) && checkIn(x.right, x.left, true);
        } else if(x.op.equals(ExprBinary.Op.NOT_EQUALS)) {
            // XXX Somewhat slower than a direct check, but avoids code reuse
            return !checkIn(x.left, x.right, true) || !checkIn(x.right, x.left, true);

        }
        else {
            return err(x);
        }
    }
    
    boolean checkIn(Expr l, Expr r, boolean sign) throws Err {        
        // IN expressions have special sugar that may need processing. 
        // If this method returns null, we're safe to do the naive thing.
        // Otherwise, we have to evaluate the desugared expression.
        Expr desugared = AmalgamVisitorHelper.isIn(l, r, true);        
        if(desugared == null) {
            Object leval = l.accept(this);
            Object reval = r.accept(this);
                 
            // May be an integer or a tupleset.
            if(leval instanceof Integer && reval instanceof Integer) {                
                return leval == reval;
            } else if(leval instanceof A4TupleSet && reval instanceof Integer) {                
                return AmalgamEvalVisitor.extractIntFromTupleSet((A4TupleSet)leval) == (Integer)reval;
            } else if(reval instanceof A4TupleSet && leval instanceof Integer) {
                return AmalgamEvalVisitor.extractIntFromTupleSet((A4TupleSet)reval) == (Integer)leval;
            } else {
                boolean in = checkIn((A4TupleSet)leval, (A4TupleSet)reval);
                if(sign) return in;
                else     return !in;    
            }            
        }
        else {
            //System.out.println("Desugared not null: L="+l+", R="+r+" ========> "+desugared);
            if(sign) return (Boolean) desugared.accept(this);
            else     return !((Boolean) desugared.accept(this));
        }                                                
    }
    
    boolean checkIn(A4TupleSet l, A4TupleSet r) throws Err {
        // Is l a subset of r? IFF L-R is empty.
        return l.minus(r).size() == 0;
    }
    
    @Override
    public Object visit(ExprBinary x) throws Err {
        debug("Visiting ExprBinary (op="+x.op+") expression ", x);
        if(lookup(x) != null) return lookup(x);
        switch(x.op) {
            case AND: 
            case OR:
            case IMPLIES:
            case IFF:
            case IN:
            case NOT_IN:
            case EQUALS:
            case NOT_EQUALS:
                return handleBinaryBoolean(x);
            case PLUS:
            case MINUS:
            case INTERSECT:
            case ARROW:
            case PLUSPLUS:
            case DOMAIN:
            case RANGE:
            case JOIN:
                return handleBinaryRelational(x);
                
            // TODO: how does this handle overflow? beware
                
            case NOT_GT:
            case LTE:                
                Integer l = AmalgamEvalVisitor.extractIntFromTupleSet(x.left.accept(this));
                Integer r = AmalgamEvalVisitor.extractIntFromTupleSet(x.right.accept(this));
                return cacheAndMaybeSanityCheck(x, l <= r);
            case NOT_LT:
            case GTE:    
                l = AmalgamEvalVisitor.extractIntFromTupleSet(x.left.accept(this));
                r = AmalgamEvalVisitor.extractIntFromTupleSet(x.right.accept(this));
                return cacheAndMaybeSanityCheck(x, l >= r);
            case NOT_GTE: 
            case LT:
                l = AmalgamEvalVisitor.extractIntFromTupleSet(x.left.accept(this));
                r = AmalgamEvalVisitor.extractIntFromTupleSet(x.right.accept(this));
                return cacheAndMaybeSanityCheck(x, l < r);
            case NOT_LTE:
            case GT:
                l = AmalgamEvalVisitor.extractIntFromTupleSet(x.left.accept(this));
                r = AmalgamEvalVisitor.extractIntFromTupleSet(x.right.accept(this));
                return cacheAndMaybeSanityCheck(x, l > r);    
                        
            default:
                return err(x);
        }
    }               
    
    public Object err(Expr x) throws Err {
        throw new ErrorFatal("AmalgamNaiveEvaluator didn't know how to handle: "+x);
    }

    @Override
    public Object visit(ExprList x) throws Err {
        debug("Visiting ExprList expression ", x);
        if(lookup(x) != null) return lookup(x);
        switch(x.op) {
            case AND: 
                for(Expr child: x.args) {
                    Boolean c = (Boolean) child.accept(this);
                    if(!c) return  cacheAndMaybeSanityCheck(x, false);
                }
                return cacheAndMaybeSanityCheck(x, true); // all children true?
            case OR:
                for(Expr child: x.args) {
                    Boolean c = (Boolean) child.accept(this);
                    if(c) return  cacheAndMaybeSanityCheck(x, true);
                }
                return cacheAndMaybeSanityCheck(x, false); // any child true?
            case TOTALORDER: 
                // Largely taken from TranslateAlloyToKodkod's visitor for this case
                return cacheAndMaybeSanityCheck(x, AmalgamVisitorHelper.desugarTOTALORDER(x).accept(this));
                
            case DISJOINT:                                 
                Expr desugared = AmalgamVisitorHelper.desugarDISJOINT(x);
                return cacheAndMaybeSanityCheck(x, desugared.accept(this));
            default:
                return err(x);
        } 
    }

    @Override
    public Object visit(ExprCall x) throws Err {
        debug("Visiting ExprCall expression ", x);
        if(lookup(x) != null) return lookup(x);
        return  cacheAndMaybeSanityCheck(x, AmalgamVisitorHelper.resolveExprCall(x).accept(this)); 
    }

    @Override
    public Object visit(ExprConstant x) throws Err {
        debug("Visiting ExprConstant expression ", x); 
        if(lookup(x) != null) return lookup(x);
        return soln.eval(x); 
    }

    @Override
    public Object visit(ExprITE x) throws Err {
        debug("Visiting ExprITE expression ", x); 
        if(lookup(x) != null) return lookup(x);
        Boolean cond = (Boolean) x.cond.accept(this);        
        if(cond) return  cacheAndMaybeSanityCheck(x, x.left.accept(this));
        else     return  cacheAndMaybeSanityCheck(x, x.right.accept(this));        
    }

    @Override
    public Object visit(ExprLet x) throws Err {     
        debug("Visiting ExprLet expression ", x); 
        if(lookup(x) != null) return lookup(x);
        Expr desugared = x.sub.accept(new AmalgamSubstituteVisitor(x.var, x.expr, false));
        return  cacheAndMaybeSanityCheck(x, desugared.accept(this));
    }

    @Override
    public Object visit(ExprQt x) throws Err {
        debug("Visiting ExprQt expression ", x);
        if(lookup(x) != null) return lookup(x);
           
        if(x.op.equals(ExprQt.Op.COMPREHENSION)) {
            return visitComprehension(x);
        } else if(x.op.equals(ExprQt.Op.ALL) || x.op.equals(ExprQt.Op.SOME) ||
                  x.op.equals(ExprQt.Op.ONE) || x.op.equals(ExprQt.Op.NO) || x.op.equals(ExprQt.Op.LONE)) {
            Expr desugaredExpr = AmalgamVisitorHelper.desugarQuantifier(x);
            debug("ExprQt desugared to ", desugaredExpr);
            if(desugaredExpr instanceof ExprQt) {
                ExprQt desugared = (ExprQt)desugaredExpr;
                // Make sure not to use "x" here!
                A4TupleSet candidates = (A4TupleSet) desugared.decls.get(0).expr.accept(this);                   
                for(A4Tuple t : candidates) {
                    Expr tExpr = AmalgamVisitorHelper.tuple2Expr(soln, t);
                    Expr subs = desugared.sub.accept(new AmalgamSubstituteVisitor(desugared.decls.get(0).names.get(0), tExpr, false));
                    Boolean res = (Boolean) subs.accept(this);
                    if(desugared.op.equals(ExprQt.Op.SOME) && res) return  cacheAndMaybeSanityCheck(x, true);
                    if(desugared.op.equals(ExprQt.Op.ALL) && !res) return  cacheAndMaybeSanityCheck(x, false);                    
                }
                if(desugared.op.equals(ExprQt.Op.SOME))     return  cacheAndMaybeSanityCheck(x, false);
                else if(desugared.op.equals(ExprQt.Op.ALL)) return  cacheAndMaybeSanityCheck(x, true);
                else                                        return err(desugared);
            } else {
                // E.g., originally a "one" quantifier, will desugar to an /\
                return  cacheAndMaybeSanityCheck(x, desugaredExpr.accept(this));
            }

        } else {
            return err(x); 
        }
    }        

    /*
    private A4TupleSet visitSum(ExprQt x) throws Err {
        throw new ErrorFatal("sum numeric operator not yet supported by Amalgam");  
    }
    */

    private Object visitComprehension(ExprQt x) throws Err {
        // Naive comprehension: try all tuples in upper-bound
        // some duplicate code w/ AmalgamVisitorHelper.desugarComprehension
        
        Expr fullTypeExpr = null;        
        List<ExprHasName> vars = new ArrayList<ExprHasName>(5); // likely not >5
        for(Decl d : x.decls) {
            if(d.disjoint != null || d.disjoint2 != null) 
                throw new ErrorFatal("comprehension decl included disj keyword, unsupported by Amalgam at present: "+x);

            for(ExprHasName v : d.names) {                                
                // once for each name in this Decl
                Expr thisTypeExpr = d.expr;
                if(thisTypeExpr instanceof ExprUnary) {
                    if(((ExprUnary)thisTypeExpr).op.equals(ExprUnary.Op.ONEOF))
                        thisTypeExpr = ((ExprUnary)thisTypeExpr).sub;
                    else if(((ExprUnary)thisTypeExpr).op.equals(ExprUnary.Op.SOMEOF) || 
                            ((ExprUnary)thisTypeExpr).op.equals(ExprUnary.Op.SETOF) ||
                            ((ExprUnary)thisTypeExpr).op.equals(ExprUnary.Op.LONEOF))
                        throw new ErrorFatal("Amalgam: unsupported multiplicity in type of comprehension: "+x+" ; "+d.expr);
                }

                if(fullTypeExpr == null) fullTypeExpr = thisTypeExpr;
                else fullTypeExpr = fullTypeExpr.product(thisTypeExpr);
                vars.add(v);
            }                        
        }        
         
        //System.out.println(fullTypeExpr);
        //System.out.println(vars);
        
        A4TupleSet possibilities = (A4TupleSet) fullTypeExpr.accept(this); 
        //System.out.println(possibilities);
        
        // Empty set to start
        A4TupleSet result = new A4TupleSet(new TupleSet(possibilities.debugGetKodkodTupleset().universe(), 
                                                        possibilities.debugGetKodkodTupleset().arity()), soln);
        
        for(A4Tuple t : possibilities) {
            Map<ExprHasName, Expr> substitutions = new HashMap<ExprHasName, Expr>();            
            List<Expr> te = AmalgamVisitorHelper.tuple2ExprVector(soln, t);
            if(vars.size() != te.size()) throw new ErrorFatal("Substitution in evaluating comprehension failed; arity mismatch: "+x);
            for(int i=0;i<vars.size();i++) {
                substitutions.put(vars.get(i), te.get(i));
            }            
            Expr substituted = x.sub.accept(new AmalgamSubstituteVisitor(substitutions, false));
            Boolean thisResult = (Boolean) substituted.accept(this);
            if(thisResult) result.mutAddTuple(t);
          //  System.out.println("t="+t+"; substituted="+substituted+"; eval to="+thisResult);
        }                
        
        return cacheAndMaybeSanityCheck(x, result);              
    }    
    
    @Override
    public Object visit(ExprUnary x) throws Err {
        debug("Visiting ExprUnary (op="+x.op+") expression: ", x);  
        if(lookup(x) != null) return lookup(x);
        Object s = x.sub.accept(this);
        
        if(x.op.equals(ExprUnary.Op.NOOP)) {
            return cacheAndMaybeSanityCheck(x, x.sub.accept(this));
        }        
        if(x.op.equals(ExprUnary.Op.SETOF)) {
            // See AmalgamEvalVisitor comments on this case
            return cacheAndMaybeSanityCheck(x, x.sub.accept(this));
        }
        if(x.op.equals(ExprUnary.Op.ONEOF)) {
            // Assume: in quantifier expr or something harmless
            // (Expressions like "A in one B" are handled in the IN case.)
            //System.out.println("ONEOF: "+x);
            return cacheAndMaybeSanityCheck(x, x.sub.accept(this));
        }
        if(x.op.equals(ExprUnary.Op.TRANSPOSE)) {
            A4TupleSet tset = (A4TupleSet)s;
            TupleSet result = new TupleSet(tset.debugGetKodkodTupleset().universe(), tset.arity());
            for(A4Tuple t : tset) {
                if(t.arity() != 2) throw new ErrorFatal("naive evaluation for "+x+"; got non binary tuple: "+t);
                // Transpose the *original* atom names, not just t.atom(1) and t.atom(0).
                Tuple to = t.getOriginalTuple();
                result.add(soln.getFactory().tuple(to.atom(1), to.atom(0)));
            }
            return cacheAndMaybeSanityCheck(x, new A4TupleSet(result, soln));
        } 
        else if(x.op.equals(ExprUnary.Op.CLOSURE)) {
            A4TupleSet ts = (A4TupleSet)s;            
            return cacheAndMaybeSanityCheck(x, new A4TupleSet(AmalgamVisitorHelper.buildClosureOfTupleSet(soln, ts.debugGetKodkodTupleset()), soln));           
        }
        else if(x.op.equals(ExprUnary.Op.RCLOSURE)) {
            // CLOSURE case plus IDEN
            A4TupleSet tset = (A4TupleSet)s;            
            TupleSet result = new TupleSet(tset.debugGetKodkodTupleset().universe(), tset.arity());
            result.addAll(AmalgamVisitorHelper.buildClosureOfTupleSet(soln, tset.debugGetKodkodTupleset()));                  
            A4TupleSet idenIs = (A4TupleSet) ExprConstant.IDEN.accept(this);
            result.addAll(idenIs.debugGetKodkodTupleset());
            return cacheAndMaybeSanityCheck(x, new A4TupleSet(result, soln));
        } 
        else if(x.op.equals(ExprUnary.Op.CAST2INT)) {            
            return cacheAndMaybeSanityCheck(x, AmalgamEvalVisitor.extractIntFromTupleSet(x.sub.accept(this)));
        }
        else if(x.op.equals(ExprUnary.Op.CAST2SIGINT)) {
            // int -> Int. If already a tuple set, we're fine. Otherwise, need to convert from Integer.
            Object res = x.sub.accept(this);
            if(res instanceof A4TupleSet) return res;
            
            Integer i = (Integer) x.sub.accept(this);                     
            Tuple t =  AmalgamEvalVisitor.buildIntTuple(soln, i);
            TupleSet ts = new TupleSet(t.universe(), 1);
            ts.add(t);
            A4TupleSet ats = new A4TupleSet(ts, soln);
            // Return A4TupleSet containing just that integer
            return cacheAndMaybeSanityCheck(x, ats);
        }     
        else if(x.op.equals(ExprUnary.Op.NOT)) {
            boolean b = (Boolean) x.sub.accept(this);
            return cacheAndMaybeSanityCheck(x, !b);
        } else if(x.op.equals(ExprUnary.Op.NO)) {         
            A4TupleSet ts = (A4TupleSet) s;            
            return cacheAndMaybeSanityCheck(x, ts.size() == 0);
        } else if(x.op.equals(ExprUnary.Op.SOME)) {         
            A4TupleSet ts = (A4TupleSet) s;            
            return cacheAndMaybeSanityCheck(x, ts.size() > 0);
        } else if(x.op.equals(ExprUnary.Op.LONE)) {         
            A4TupleSet ts = (A4TupleSet) s;            
            return cacheAndMaybeSanityCheck(x, ts.size() <= 1);
        } else if(x.op.equals(ExprUnary.Op.ONE)) {         
            A4TupleSet ts = (A4TupleSet) s;            
            return cacheAndMaybeSanityCheck(x, ts.size() == 1);
        } else if(x.op.equals(ExprUnary.Op.CARDINALITY)) {
            A4TupleSet ts = (A4TupleSet) s;
            return ts.size();
        }
        
        else {            
            return err(x);
        }
    }
           
    @Override
    public Object visit(ExprVar x) throws Err {
        if(lookup(x) != null) return lookup(x);
        return cacheAndMaybeSanityCheck(x, soln.eval(x));
    }

    @Override
    public Object visit(Sig x) throws Err {
        if(lookup(x) != null) return lookup(x);
        //System.out.println("Sig "+x+" evaluated to: "+soln.eval(x));
        //TupleSet result = (TupleSet) soln.eval(x);
        return cacheAndMaybeSanityCheck(x, soln.eval(x));
    }

    @Override
    public Object visit(Field x) throws Err {        
        if(lookup(x) != null) return lookup(x);
        //System.out.println("Field "+x+" evaluated to: "+soln.eval(x));
        return cacheAndMaybeSanityCheck(x, soln.eval(x));
    }

    public static long getSumCacheSize() {
        long result = 0;
        for(Map<Expr, Object> cache : AmalgamNaiveEvaluator.storedCaches.values()) {
            result += cache.size();
        }
        return result;
    }
 
    // FOR DEBUGGING MEMORY USAGE
    /*protected void finalize() {
        System.out.println("Finalizing AmalgamNaiveVisitor: "+this);
    }*/
    
    
}
