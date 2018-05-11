package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprQt;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4whole.AmalgamTupleInExpr;
import gnu.trove.map.hash.TCustomHashMap;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

public class AmalgamVisitorHelper {

    static boolean isGroundProduct(Expr x) {
        // Tuple buried in an Expr, like: Node$0 or Node$0 -> Node$1

        // Strip off noop, casts, if needed
        if(x instanceof ExprUnary) {
            if(((ExprUnary) x).op.equals(ExprUnary.Op.NOOP) || 
               ((ExprUnary) x).op.equals(ExprUnary.Op.CAST2INT) || 
               ((ExprUnary) x).op.equals(ExprUnary.Op.CAST2SIGINT))
            return isGroundProduct(((ExprUnary) x).sub);
        }
        if(x instanceof ExprVar) return true;
        if(x instanceof ExprBinary) {
            ExprBinary bx = (ExprBinary)x;
            if(bx.op.equals(ExprBinary.Op.ARROW)) {
                return isGroundProduct(bx.left) && isGroundProduct(bx.right);
            }            
        }
        if(x instanceof ExprConstant) {
            if(((ExprConstant)x).op.equals(ExprConstant.Op.NUMBER))
                return true;
        }
        return false;
    }

    //////////////////////////////////////////////////////////////////////////
    // AND and OR cases, taking higher-level negations into account
    static boolean isANDContext(Expr y, boolean currentSign) throws Err {
        if(y instanceof ExprBinary) {
            ExprBinary x = (ExprBinary)y;
            return (currentSign && x.op.equals(ExprBinary.Op.AND)) || (!currentSign && x.op.equals(ExprBinary.Op.OR));
        }
        else if(y instanceof ExprList) {
            ExprList x = (ExprList)y;
            return (currentSign && x.op.equals(ExprList.Op.AND)) || (!currentSign && x.op.equals(ExprList.Op.OR));
        }
        else 
            throw new ErrorFatal("isANDContext expected ExprList or ExprBinary; got: "+y);
    }
    static boolean isORContext(Expr y, boolean currentSign) throws Err {
        if(y instanceof ExprBinary) {
            ExprBinary x = (ExprBinary)y;
            return (currentSign && x.op.equals(ExprBinary.Op.OR)) || (!currentSign && x.op.equals(ExprBinary.Op.AND));
        }
        else if(y instanceof ExprList) {
            ExprList x = (ExprList)y;
            return (currentSign && x.op.equals(ExprList.Op.OR)) || (!currentSign && x.op.equals(ExprList.Op.AND));
        }
        else 
            throw new ErrorFatal("isORContext expected ExprList or ExprBinary; got: "+y);
    }

    static Tuple transposeTuple(A4Solution soln, Tuple tup) throws Err {
        if(tup.arity() != 2) throw new ErrorFatal("Attempted transposeTuple on non-binary tuple: "+tup);        
        return soln.getFactory().tuple(tup.atom(1), tup.atom(0));
    }

    static Tuple joinTuple(A4Solution soln, A4Tuple lt, A4Tuple rt) {
        return joinTuple(soln, lt.getOriginalTuple(), rt.getOriginalTuple());        
    }
    
    static Tuple joinTuple(A4Solution soln, Tuple lt, Tuple rt) {
        List<Object> newTup = new ArrayList<Object>();
        Object joinAtomL = lt.atom(lt.arity()-1);
        Object joinAtomR = rt.atom(0);

        // if these tuples don't join, return null
        if(!joinAtomL.equals(joinAtomR)) return null;

        // build new tuple lt.rt 
        for(int ii=0;ii<lt.arity()-1;ii++)
            newTup.add(lt.atom(ii));
        for(int ii=1;ii<rt.arity();ii++)
            newTup.add(rt.atom(ii)); 
        return soln.getFactory().tuple(newTup);
    }

    static Tuple projectTupleRange(A4Solution soln, Tuple t, int startIndex, int len) {
        // 0-based
        List<Object> atoms = new ArrayList<Object>();
        for(int ii=0;ii<len;ii++) 
            atoms.add(t.atom(startIndex+ii));
        return soln.getFactory().tuple(atoms);
    }

    static Tuple projectTuple(A4Solution soln, Tuple t, int singleIndex) {
        // 0-based
        return soln.getFactory().tuple(t.atom(singleIndex));
    }

    private static Expr stripMultiplicity(Expr x) {
        if(x instanceof ExprUnary) {
            ExprUnary u = (ExprUnary) x;            
            if(u.op.equals(ExprUnary.Op.ONEOF) ||  u.op.equals(ExprUnary.Op.LONEOF) ||
               u.op.equals(ExprUnary.Op.SOMEOF) || u.op.equals(ExprUnary.Op.SETOF)) {
                return ((ExprUnary)x).sub;
            }         
            if(u.op.equals(ExprUnary.Op.NOOP)) {
                return ExprUnary.Op.NOOP.make(x.pos, stripMultiplicity(u.sub));
            }
        }
        else if(x instanceof ExprBinary) {
            ExprBinary b = (ExprBinary) x;
            if(b.op.equals(ExprBinary.Op.ARROW)) {
                return b.op.make(b.pos, b.closingBracket, 
                                 stripMultiplicity(b.left), stripMultiplicity(b.right));            
            } else if(b.op.equals(ExprBinary.Op.ANY_ARROW_LONE) ||
                      b.op.equals(ExprBinary.Op.ANY_ARROW_ONE) ||
                      b.op.equals(ExprBinary.Op.ANY_ARROW_SOME) ||
                      b.op.equals(ExprBinary.Op.LONE_ARROW_ANY) ||
                      b.op.equals(ExprBinary.Op.LONE_ARROW_LONE) ||
                      b.op.equals(ExprBinary.Op.LONE_ARROW_ONE) ||
                      b.op.equals(ExprBinary.Op.LONE_ARROW_SOME) ||
                      b.op.equals(ExprBinary.Op.ONE_ARROW_ANY) ||
                      b.op.equals(ExprBinary.Op.ONE_ARROW_LONE) ||
                      b.op.equals(ExprBinary.Op.ONE_ARROW_ONE) ||
                      b.op.equals(ExprBinary.Op.ONE_ARROW_SOME) ||               
                      b.op.equals(ExprBinary.Op.SOME_ARROW_ANY) ||
                      b.op.equals(ExprBinary.Op.SOME_ARROW_LONE) ||
                      b.op.equals(ExprBinary.Op.SOME_ARROW_ONE) ||
                      b.op.equals(ExprBinary.Op.SOME_ARROW_SOME)) {
                return ExprBinary.Op.ARROW.make(b.pos, b.closingBracket, b.left, b.right);
            }
        }
        return x;
    }

    // EvalVisitor expects null if desugared, so default branch returned null.
    // ...but isInBinary may recur on isIn, expecting the Op.IN.make... result. 
    static Expr isIn(Expr a, Expr right, boolean first) throws Err {
        //System.err.println("isIn: "+a+"; "+right);
        if (right instanceof ExprBinary && right.mult!=0 && ((ExprBinary)right).op.isArrow) {
            // Handles possible "binary" or higher-arity multiplicity
            return isInBinary(a, (ExprBinary)right);
        }
        else {
            Expr b = stripMultiplicity(right);            
            switch(right.mult()) {
            case EXACTLYOF: return ExprBinary.Op.EQUALS.make(a.pos(), a.closingBracket, a, b);
            case ONEOF:     return ExprBinary.Op.AND.make(a.pos(), a.closingBracket, a.one(), a.in(b));
            case LONEOF:    return ExprBinary.Op.AND.make(a.pos(), a.closingBracket, a.lone(), a.in(b));
            case SOMEOF:    return ExprBinary.Op.AND.make(a.pos(), a.closingBracket, a.some(), a.in(b));
            // XXX TN: why did we have this null returning default case in Oct? Replaced it with expected IN expression
            //default:        System.err.println("In isIn for "+a+", "+right+"; right.mult()="+right.mult()+"; returning null..."); return null;
            default:        
                if(first) return null;
                else return ExprBinary.Op.IN.make(a.pos(), a.closingBracket, a, b);
            }
        }
    }

    // See TranslateAlloyToKodkod.isIn
    //   ^ this method handles unary-expression desugaring
    //   calls isInBinary otherwise, which handles this *and* complex arrow types

    // See TranslateAlloyToKodkod.isInBinary 
    // TN: r: "R" the left hand side of the containment
    // TN: ab: the binary right hand side
    private static Expr isInBinary(Expr r, ExprBinary ab) throws Err {
        final Expr a=ab.left, b=ab.right;
        List<Decl> d=null, d2=null;
        Expr ans1, ans2;

        /////////////////////// TN's separation ///////////////////

        // "R in A ->op B" means for each tuple a in A, there are "op" tuples in r that begins with a.
        Expr atuple=null, ar=r;
        for(int i=a.type().arity(); i>0; i--) {
            String vname = "v" + Integer.toString(TranslateAlloyToKodkod.cnt++);
            if (!TranslateAlloyToKodkod.am) {
                throw new ErrorFatal("Expected AM set to true.");
                // if (a.type().arity()==1) d=v.oneOf(a); else if (d==null) d=v.oneOf(Relation.UNIV); else d=v.oneOf(Relation.UNIV).and(d);
            } else {
                d = am(a, d, i, vname);
            }
                
            ExprHasName v = d.get(d.size()-1).names.get(0);
            ar=v.join(ar);
            if (atuple==null) atuple=v; else atuple=atuple.product(v);
        }
        ans1=isIn(ar, ab.right,false);        
        switch(ab.op) {
        case ISSEQ_ARROW_LONE:
        case ANY_ARROW_LONE: case SOME_ARROW_LONE: case ONE_ARROW_LONE: case LONE_ARROW_LONE: ans1=ar.lone().and(ans1); break;
        case ANY_ARROW_ONE:  case SOME_ARROW_ONE:  case ONE_ARROW_ONE:  case LONE_ARROW_ONE:  ans1=ar.one().and(ans1);  break;
        case ANY_ARROW_SOME: case SOME_ARROW_SOME: case ONE_ARROW_SOME: case LONE_ARROW_SOME: ans1=ar.some().and(ans1); break;
        default: break;
        }                
        if (a.type().arity()>1) { Expr tmp=isIn(atuple, ab.left,false); if (tmp!=ExprConstant.TRUE) ans1=tmp.implies(ans1); }
        ans1= ExprQt.Op.ALL.make(ab.pos, ab.closingBracket, d, ans1);

        
        /////////////////////// TN's separation ///////////////////

        //ans1=ans1.forAll(d); // TN: was this
        // "R in A op-> B" means for each tuple b in B, there are "op" tuples in r that end with b.
        Expr btuple=null, rb=r;
        for(int i=b.type().arity(); i>0; i--) {
            String vname = "v" + Integer.toString(TranslateAlloyToKodkod.cnt++);
            if (!TranslateAlloyToKodkod.am) {
                throw new ErrorFatal("Expected AM set to true.");
                // if (b.type().arity()==1) d2=v.oneOf(b); else if (d2==null) d2=v.oneOf(Relation.UNIV); else d2=v.oneOf(Relation.UNIV).and(d2);
            } else {
                d2 = am(b, d2, i, vname);
            }
            ExprHasName v = d2.get(d2.size()-1).names.get(0);
            rb=rb.join(v);
            if (btuple==null) btuple=v; else btuple=v.product(btuple);
        }
        ans2=isIn(rb, ab.left,false);        
        switch(ab.op) {
        case LONE_ARROW_ANY: case LONE_ARROW_SOME: case LONE_ARROW_ONE: case LONE_ARROW_LONE: ans2=rb.lone().and(ans2); break;
        case ONE_ARROW_ANY:  case ONE_ARROW_SOME:  case ONE_ARROW_ONE:  case ONE_ARROW_LONE:  ans2=rb.one().and(ans2);  break;
        case SOME_ARROW_ANY: case SOME_ARROW_SOME: case SOME_ARROW_ONE: case SOME_ARROW_LONE: ans2=rb.some().and(ans2); break;
        default: break;
        }
        if (b.type().arity()>1) { Expr tmp=isIn(btuple, ab.right,false); if (tmp!=ExprConstant.TRUE) ans2=tmp.implies(ans2); }
        // ans2=ans2.forAll(d2); // TN: was this
        ans2= ExprQt.Op.ALL.make(ab.pos, ab.closingBracket, d2, ans2);        
        // Now, put everything together 
        // TN: need to strip multiplicity explicitly; Translate didn't need to because it produced Kodkod expressions
        Expr sa = stripMultiplicity(a);
        Expr sb = stripMultiplicity(b);
        //System.out.println(">>>>>sa="+sa);
        //System.out.println(">>>>>sb="+sb);
        Expr ans=r.in(sa.product(sb)).and(ans1).and(ans2);          
        if (ab.op==ExprBinary.Op.ISSEQ_ARROW_LONE) {
            throw new ErrorFatal("Amalgam desugaring does not support ISSEQ_ARROW_LONE operator.");
            /*Expr rr=r;
            while(rr.type().arity()>1) rr=rr.join(Sig.UNIV);
            ans=rr.difference(rr.join(A4Solution.KK_NEXT)).in(A4Solution.KK_ZERO).and(ans);*/
        }
        return ans;
    }

    // TN changed Decls to List<Decl>
    private static List<Decl> am(final Expr a, List<Decl> d, int i, String vlabel) throws Err {
        Expr colType;
        if (a.type().arity() == 1) {
            assert i == 1; 
            colType = a;
        } else {
            // colType = a.project(IntConstant.constant(i - 1))); //UNSOUND
            colType = Sig.UNIV; // TN: was Relation.UNIV;
        }

        if(d == null) {
            //v.oneOf(colType)
            Decl newd = colType.oneOf(vlabel);
            List<Decl> result = new ArrayList<Decl>();
            result.add(newd);
            return result;
        } else {
            Decl newd = colType.oneOf(vlabel);
            d.add(newd);
            return d;
        }

        // TN: was this
        //return (d == null) ? v.oneOf(colType)   
        //: d.and(v.oneOf(colType));
    }


    /*   static List<Expr> flattenProduct(Expr e) {
        List<Expr> result = new ArrayList<Expr>();
        if(!(e instanceof ExprBinary))
        {
            result.add(e);
        }
        else if(((ExprBinary)e).op.equals(ExprBinary.Op.ARROW)) {
            result.addAll(flattenProduct(((ExprBinary)e).left));
            result.addAll(flattenProduct(((ExprBinary)e).right));
        } 
        else
        {
            result.add(e);
        }
        return result;
    }

    static boolean isMultiplicityRHSIn(ExprBinary x) {
        // RHS is something like "one A"
        if(x.right instanceof ExprUnary) {
            ExprUnary r = (ExprUnary)x.right;
            if(r.op.equals(ExprUnary.Op.LONEOF) ||
               r.op.equals(ExprUnary.Op.ONEOF) ||
               r.op.equals(ExprUnary.Op.SOMEOF))
                return true;
        }
        // RHS is something like "A -> one B -> one C"
        if(x.right instanceof ExprBinary) {
            List<Expr> flattened = flattenProduct(x.right);            
            for(Expr sub : flattened) {
                if(sub instanceof ExprUnary) {
                    ExprUnary usub = (ExprUnary) sub;
                    if(usub.op.equals(ExprUnary.Op.LONEOF) ||
                       usub.op.equals(ExprUnary.Op.ONEOF) ||
                       usub.op.equals(ExprUnary.Op.SOMEOF))
                             return true;
                }
            }
        }

        return false;
    }
     */ 
    
    ////////////////////////////////////////////////////
    
    static ExprQt splitMultipleVarsInQt(ExprQt x) throws Err {
        // This is semantically correct only for "some" and "all" quantifiers.
        // some x: A,y: B | ...   -----> some x : A | ... 
        // some x,y: T | ...   -----> some x : T | ...
        
        if(!ExprQt.Op.ALL.equals(x.op) && !ExprQt.Op.SOME.equals(x.op)) {
            throw new ErrorFatal("splitMultipleVarsInQt without desugaring non-some/all quantifier first: "+x);
        }

        if(x.decls.size() == 1 && x.decls.get(0).names.size() == 1)
            return x;

        // Variables will be the same; just split up the quantifier decls themselves.
        List<Decl> newDecls = new ArrayList<Decl>();

        for(Decl d : x.decls) {
            if(d.disjoint2 != null) { 
                throw new ErrorFatal("quantifier decl included disjoint2, unsupported by Amalgam at present: "+x);
            }

            // in case of disj
            Set<ExprHasName> priors = new HashSet<ExprHasName>();
            for(ExprHasName v : d.names) {
                // duplicate code with Expr.someOf (but want to *reuse* the inner expr, since that's where some/lone/etc get saved)
                Decl newDecl;
                if(d.disjoint != null && priors.size() > 0) {
                    // add "-T" for every prior T in this decl                    
                    Expr priorUnion = null;
                    for(Expr prior : priors) {                                                                      
                        if(priorUnion == null) priorUnion = prior;
                        else priorUnion = priorUnion.plus(prior);
                    }
                    
                    // Extract decl's actual type + multiplicity
                    ExprUnary.Op dop;
                    Expr e;                    
                    if((d.expr instanceof ExprUnary) &&
                         (((ExprUnary)d.expr).op.equals(ExprUnary.Op.ONEOF) ||                            
                         ((ExprUnary)d.expr).op.equals(ExprUnary.Op.SOMEOF) || 
                         ((ExprUnary)d.expr).op.equals(ExprUnary.Op.SETOF) ||
                         ((ExprUnary)d.expr).op.equals(ExprUnary.Op.LONEOF))) {
                             dop = ((ExprUnary)d.expr).op;
                             e = ((ExprUnary)d.expr).sub;
                    } else {
                         throw new ErrorFatal("Amalgam: decl had unexpected unary op: "+x+" ; "+d.expr);   
                    }                                                                  
                    if(ExprUnary.Op.ONEOF.equals(dop))
                        newDecl = new Decl(null, null, null, Arrays.asList(v), e.minus(priorUnion).oneOf());
                    else if(ExprUnary.Op.SOMEOF.equals(dop))
                        newDecl = new Decl(null, null, null, Arrays.asList(v), e.minus(priorUnion).someOf());
                    else if(ExprUnary.Op.SETOF.equals(dop))
                        newDecl = new Decl(null, null, null, Arrays.asList(v), e.minus(priorUnion).setOf());
                    else if(ExprUnary.Op.LONEOF.equals(dop))
                        newDecl = new Decl(null, null, null, Arrays.asList(v), e.minus(priorUnion).loneOf());
                    else {
                        throw new ErrorFatal("Amalgam: decl had unexpected unary op: "+x+" ; "+d.expr);   
                    }                    
                } else {
                    newDecl = new Decl(null, null, null, Arrays.asList(v), d.expr);
                }
                newDecls.add(newDecl);
                priors.add(v);
            }
            
            
        }
        
        //System.err.println("Desugaring multi-decl/var ExprQt: "+x);        

        Expr desugared = x.sub;
        // we're about to build the quantifiers inside out, so reverse order (someone may have written all x:T,y:T-x ...)
        Collections.reverse(newDecls);
        for(Decl d : newDecls) {        
            // Manufacture a new position for each desugared quantifier
            Pos newPos = new Pos(x.pos.filename, d.names.get(0).pos.x, d.names.get(0).pos.y, x.pos.x2, x.pos.y2);
            desugared = x.op.make(newPos, null, Util.asList(d), desugared);
        }
        //System.err.println("Result was: "+desugared);

        return (ExprQt)desugared;
    }

    static public final SpanIndependentExprHashingStrategy strat = new SpanIndependentExprHashingStrategy();
    
    // Substitute to eliminate the predicate or function call this represents.
    // Static member field cache since any specific call should always be resolved the same way

    static Map<ExprCall, Expr> resolvedCache = new TCustomHashMap<ExprCall, Expr>(strat, 1000);
    static public long getResolvedCacheSize() {
        return resolvedCache.size();
    }
    static public void clearResolvedCache() {
        resolvedCache.clear();
    }
    
    static Expr resolveExprCall(ExprCall c) throws Err {                        
        if(resolvedCache.containsKey(c))
            return resolvedCache.get(c);
        if(c.fun.count() != c.args.size()) 
            throw new ErrorFatal("ExprCall had wrong number of arguments: "+c);

        Expr result = c.fun.getBody();
        for(int iArg = 0; iArg<c.fun.count();iArg++) {
            ExprVar from = c.fun.get(iArg);
            Expr to = c.args.get(iArg);
            result = result.accept(new AmalgamSubstituteVisitor(from, to, false));
        }

        //System.err.println("resolveExprCall: "+c+"; pos="+c.pos.toString());
        //System.err.println("produced pos="+result.pos.toString());        
        
        resolvedCache.put(c, result);
        return result;
    }

    /**
     * Desugar into some number of single variable some/alls.  
     * The "lone" quantifier case produces a disjunction, hence why this method can't return ExprQt
     */
    static Expr desugarQuantifier(ExprQt x) throws Err {        

        // This method should inspect operators directly, NOT call the context predicates, 
        // because it is desugaring and so cares about syntax not semantics with respect to current sign.

        // Step one: first desugar out non-all/some quantifiers
        // Step two: separate multi-var decls
        // If these steps are reversed, will possibly violate semantics
        // (note: no x,y: A ... is not equalivalent to no x:A | no y:A: | ...)
        
        ///////////////////
        // Step (1) 

        if(x.op.equals(ExprQt.Op.ALL)) {
            Expr result = splitMultipleVarsInQt(x); 
            //System.err.println("desugared ALL quantifier (returning):\n"+x+" to \n"+result);
            return result;            
        } else if(x.op.equals(ExprQt.Op.SOME)) {
            Expr result = splitMultipleVarsInQt(x); 
            //System.err.println("desugared SOME quantifier (returning):\n"+x+" to \n"+result);
            return result;            
           
        } else if(x.op.equals(ExprQt.Op.LONE)) {
            //  Use "oneOf" here, not "someOf": "someOf" is higher-order quantification.
            //   This is the multiplicity vs. quantifier distinction: \exists x : some T looks for a *set* x.
            // do not break off first decl only; that won't be sound either
            // Need to turn this into an all with double the decls
            
            // for 2nd half in "all": substituted fmla, decls, etc.
            List<Decl> decls2 = new LinkedList<Decl>();
            Map<ExprHasName, ExprHasName> vars2 = new HashMap<ExprHasName,ExprHasName>();
            for(Decl d : x.decls) {
                
                List<ExprHasName> newNames = new LinkedList<ExprHasName>();                
                for(ExprHasName v: d.names) {
                    // Need to give this ExprVar a type, or else we will get an error on creation.
                    // Reuse the type of v
                    vars2.put(v, ExprVar.make(v.pos, v.label+"_LONE", v.type()));    
                    newNames.add(vars2.get(v));
                }
                
                d.expr.oneOf("foo");
                
                // substitute for *all prior decls* and this one (hence passing full vars2 map)
                Expr expr2 = d.expr.accept(new AmalgamSubstituteVisitor(vars2, false));                
                Decl d2 = new Decl(d.isPrivate, d.disjoint, d.disjoint2, newNames, expr2);    
                decls2.add(d2);
            }
            Expr fmla2 = x.sub.accept(new AmalgamSubstituteVisitor(vars2, false));
            
            List<Decl> bothdecls = new LinkedList<Decl>(x.decls);
            bothdecls.addAll(decls2);
            
            // build => x1=x1_LONE /\ x2=x2_LONE /\ ...
            List<Expr> conjuncts = new ArrayList<Expr>(x.decls.size());
            for(ExprHasName v1 : vars2.keySet()) {               
               conjuncts.add(v1.equal(vars2.get(v1)));               
            }
            
            Expr subExpr = x.sub.and(fmla2).implies(ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, conjuncts));
            ExprQt desugared = (ExprQt) ExprQt.Op.ALL.make(x.pos, x.closingBracket, bothdecls, subExpr);
            //System.err.println("desugared LONE quantifier (about to desugar further):\n"+x+" to \n"+desugared);            
            return desugarQuantifier(desugared);                        
        } else if(x.op.equals(ExprQt.Op.ONE)) {
            // desugar: lone and some
            ExprQt pt1 = (ExprQt)ExprQt.Op.LONE.make(x.pos, x.closingBracket, x.decls, x.sub);
            pt1 = (ExprQt)desugarQuantifier(pt1);
            ExprQt pt2 = (ExprQt)ExprQt.Op.SOME.make(x.pos, x.closingBracket, x.decls, x.sub);
            pt2 = (ExprQt)desugarQuantifier(pt2);            
            Expr desugared = pt1.and(pt2); // lone and some
            //System.err.println("desugared ONE quantifier (returning): "+x+" to \n"+desugared);
            return desugared;            
        } else if(x.op.equals(ExprQt.Op.NO)) {
            // DESUGAR: all xs: T | ~F(xs)            
            Expr desugaredResult = desugarQuantifier((ExprQt)ExprQt.Op.ALL.make(x.pos, x.closingBracket, x.decls, x.sub.not()));
            //System.err.println("desugared NO quantifier (returning):\n"+x+" to \n"+desugaredResult);
            return desugaredResult; 
                    
        } else {
            throw new ErrorFatal("unexpected operator in ExprQt visit: "+x);
        }                        
    }

    public static Expr desugarComprehension(A4Solution orig, ExprQt x, Tuple currentTupleIfAtomic) throws Err {        
        if(currentTupleIfAtomic == null)
            throw new ErrorFatal("Amalgam: desugarComprehension given null tuple.");        
        
        // ith tuple component gets substituted for ith variable in decls
        // need to make sure each component is appropriate type, too
        Expr substituted = x.sub;
        Expr fullTypeExpr = null;
        int ii = 0;
        for(Decl d : x.decls) {
            if(d.disjoint != null || d.disjoint2 != null) 
                throw new ErrorFatal("comprehension decl included disj keyword, unsupported by Amalgam at present: "+x+" ; "+currentTupleIfAtomic);

            for(ExprHasName v : d.names) {                
                if(ii >= currentTupleIfAtomic.arity())
                    throw new ErrorFatal("comprehension decls exceeded context tuple arity: "+x+" ; "+currentTupleIfAtomic);

                Expr tupExpr = tuple2Expr(orig, projectTuple(orig, currentTupleIfAtomic, ii));
                substituted = substituted.accept(new AmalgamSubstituteVisitor(v, tupExpr, false));

                ii++;

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
            }                        
        }        

        List<Expr> lst = new ArrayList<Expr>(2);
        lst.add(substituted); 
        lst.add(tuple2Expr(orig, currentTupleIfAtomic).in(fullTypeExpr)); // check tuple has declared type
        Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, lst);        
        //System.err.println("Desugared comprehension: "+currentTupleIfAtomic+" in "+x+"  -> "+desugared);
        return desugared;
    }


    static ExprHasName getQtSingleVar(ExprQt x) throws Err {
        if(x.decls.size() > 1) 
            throw new ErrorFatal("ExprQt had >1 decl, unexpected by getQtSingleVar: "+x);   
        for(Decl d : x.decls) {            
            if(d.disjoint != null || d.disjoint2 != null) 
                throw new ErrorFatal("ExprQt with disjointness not supported yet: "+d);                            
            if(d.names.size() > 1) 
                throw new ErrorFatal("ExprQt had >1 name in a decl, unexpected by getQtSingleVar: "+x);

            for(ExprHasName n : d.names) {
                return n;
            }
        }
        throw new ErrorFatal("getQtSingleVar found no variable: "+x);
    }

    static Expr getQtSingleVarExpr(ExprQt x) throws Err {
        if(x.decls.size() > 1) 
            throw new ErrorFatal("ExprQt had >1 decl, unexpected by getQtSingleVarExpr: "+x);   
        for(Decl d : x.decls) {  
            // Beware, this may be a default "one" etc. rather than the raw expression:
            if(d.expr instanceof ExprUnary) {
                ExprUnary unaryexpr = (ExprUnary)d.expr; 
                if(unaryexpr.op.equals(ExprUnary.Op.ONEOF)) {
                    return unaryexpr.sub;
                }
                else if(unaryexpr.op.equals(ExprUnary.Op.LONEOF)) {
                    throw new ErrorFatal("Quantification over LONEOF unsupported by Amalgam: "+x);
                }
                // Someof and Setof are higher-order quantification                 
                else if(unaryexpr.op.equals(ExprUnary.Op.SOMEOF) ||                                        
                        unaryexpr.op.equals(ExprUnary.Op.SETOF)) {
                    //debug("getQtSingleVarExpr found X-of unary expr: "+x+"; removing a layer and returning "+unaryexpr.sub);
                    throw new ErrorFatal("Higher-order quantification unsupported by Amalgam: "+x+"; multiplicity was: "+unaryexpr.op);                   
                }
            }
            return d.expr;
        }
        throw new ErrorFatal("getQtSingleVarExpr found no variable: "+x);
    }

    static public Expr tuple2Expr(A4Solution orig, Tuple tup) throws Err {
        // TODO: is this safe? no reference-equality issues?
        // TN: ~~IMPORTANT~~ Passing from Kodkod Tuple to A4Tuple changes the atom() method somewhat.
        // Kodkod tuple will just return the atom.
        // A4Tuple will return the atom *AFTER* passing it through atom2name.
        //    (and if it doesn't have a key there, it will just return the atom.)
        A4Tuple a4tup = new A4Tuple(tup, orig);            
        return tuple2Expr(orig, a4tup);
    }

    /** Print debugging information for diff eval visitor */
    public static final boolean debugDiffEval = false;
    /** Print debugging information for literal-provenance visitor */
    public static final boolean debugGround = false;
    /** Print debugging information for upper-bound visitor */
    public static final boolean debugUB = false;
    
    /** Print debugging information for naive evaluation */
    public static final boolean debugNEVAL = false;
    
    /** For non-visitor module debugging info */
    public static final boolean debugOther = false;
    public static final boolean debugt2e = false;
    
    /** If true, every node visited will be sanity-checked to ensure it evaluates differently in the two models. */
    public static final boolean sanityCheck = true;
    
    // Different models may produce different entries.
    // XXX Really, we should have canonicity at the _spec_ level.
    static Map<A4Solution, Map<String, Expr>> tuple2ExprCache = new HashMap<A4Solution, Map<String, Expr>>();
    
    public static long getExprCacheSize() {
        return tuple2ExprCache.size();
    }
    
    static public void clearExprCache() {
        tuple2ExprCache.clear();  
    }
    
    static void cacheTuple2ExprIfNeeded(A4Solution orig, String name) {
        if(!tuple2ExprCache.containsKey(orig))
            tuple2ExprCache.put(orig, new HashMap<String, Expr>());
        
        Map<String, Expr> modelCache = tuple2ExprCache.get(orig);
        
        if(modelCache.containsKey(name))
            return;
        
        // Check whether integer atom
        boolean isNum = false;
        int num = 0;
        try {
            num = Integer.parseInt(name);
            isNum = true;                
        } catch(NumberFormatException e) {}
                
        // If integer, just create the constant. Otherwise, find the correct ExprVar for this atom
        if(isNum) {
            Expr e = ExprConstant.makeNUMBER(num);
            modelCache.put(name, e);
        } else {      
            // ans.getAllAtoms() contains ExprVar for each atom. Find the correct one for this atom.
            for(ExprVar a : orig.getAllAtoms()) {
                String alabel = a.label;               
                if(alabel.equals(name)) {
                    if(debugt2e) System.err.println("tuple2Expr found ExprVar for atom (post atom2name): "+name+": "+a);                    
                    modelCache.put(name, a);
                    break;
                }
            } // end loop for each ExprVar 
        } // end non-number case       
    }
    
    static public List<Expr> tuple2ExprVector(A4Solution orig, A4Tuple tup) throws ErrorFatal {
        // Note near-identical structure (and WARNINGS! see comments) vs. tuple2Expr.
        List<Expr> result = new ArrayList<Expr>(tup.arity());
        
        for(int ii=0;ii<tup.arity();ii++) {            
            String name = tup.atom(ii);
            cacheTuple2ExprIfNeeded(orig, name);            
            Map<String, Expr> modelCache = tuple2ExprCache.get(orig);            
            if(modelCache.containsKey(name)) {                
                result.add(modelCache.get(name));                
            } else {
                throw new ErrorFatal("tuple2ExprVector: unable to find atomic sig in passed instance for (post atom2name): "+name); 
            }
        }
                
        return result;        
    }
    
    static public Expr tuple2Expr(A4Solution orig, A4Tuple tup) throws Err {
        Expr product = null;

        /*
         * We are working with an A4Tuple, not a Kodkod Tuple. 
         * That means it is _vital_ to use tup.atom(ii) and not orig.atom2name(tup.atom(ii))
         * or else we will rename a 2nd time...
         */

        for(int ii=0;ii<tup.arity();ii++) {
            String name = tup.atom(ii);
            // DO NOT CALL THIS, see comment above
            // String name = orig.atom2name(tup.atom(ii));
            cacheTuple2ExprIfNeeded(orig, name);            
            Map<String, Expr> modelCache = tuple2ExprCache.get(orig);            
            if(modelCache.containsKey(name)) {
                if(product == null) product = modelCache.get(name);
                else product = product.product(modelCache.get(name));                
            } else {
                System.err.println("Error context: atoms="+orig.getAllAtoms()+" inst="+orig.debugExtractKInstance());
                throw new ErrorFatal("tuple2Expr: unable to find atomic sig in passed instance for (post atom2name): "+name); 
            }
        }
                
        return product;            
    }

    public static Set<List<Object>> buildSimplePaths(Object source, Object destination, TupleSet ub, Set<Object> seen) {
        Set<List<Object>> result = new HashSet<List<Object>>();
        seen.add(source);        

        for(Tuple tup : ub) {            
            if(source.equals(tup.atom(0))) {
                Object nextsource = tup.atom(1);

                // base case: directly accessible
                if(destination.equals(nextsource)) {
                    List<Object> thisHop = new ArrayList<Object>();
                    thisHop.add(source); thisHop.add(destination);
                    result.add(thisHop);
                    continue; // search for other paths, too.
                }

                // This tuple works as an initial hop. recur and combine                
                if(!seen.contains(nextsource)) { // forbid cycles                
                    Set<List<Object>> subpaths = buildSimplePaths(nextsource, destination, ub, seen);
                    for(List<Object> subpath : subpaths) {
                        subpath.add(0, source);
                        result.add(subpath);
                    }
                }
            }
        }

        seen.remove(source);
        return result;        
    }

    public static Expr eliminateDoubleNegation(Expr e) {
        e = e.deNOP();
        if(e instanceof ExprUnary && ((ExprUnary) e).op.equals(ExprUnary.Op.NOT)) {
            Expr inner = ((ExprUnary) e).sub.deNOP();
            if(inner instanceof ExprUnary && ((ExprUnary) inner).op.equals(ExprUnary.Op.NOT)) {
                return eliminateDoubleNegation(((ExprUnary) inner).sub);
            }
        }
        return e;
    }

    public static boolean literalExprEquals(A4Solution orig, AmalgamTupleInExpr lit, boolean flip, Expr x) throws Err {
        //System.err.println(lit+" = "+x);
        // i dont trust this implementation
        boolean eq = false;
        if(x instanceof ExprBinary) {
            ExprBinary bin = (ExprBinary) x;
            if(bin.op==ExprBinary.Op.IN) {
                Expr tlit = tuple2Expr(orig, lit.t);
                if(flip) tlit = tlit.not();
                Expr tx = bin.left;
                Expr rlit = lit.e;
                Expr rx = bin.right;
                boolean teq = tx.equals(tlit);
                boolean req = rx.equals(rlit);
                eq = teq&&req;
            }
        }
        return eq;
    }

    public static boolean containsExpr(Iterable<Expr> explain, Expr e) {
        boolean c = false;
        for(Expr x : explain) {
            c |= x.toString().equals(e.toString());
        }
        return c;
    }

    public static Provenance reduceExplain(Provenance explain) {
        List<Expr> reduce = new ArrayList<Expr>();
        for(Expr e : explain.alphas) { 
            if(!e.toString().equals("true") && !containsExpr(reduce, e)) {
                reduce.add(e);
            }
        }
        return new Provenance(reduce, explain.bindings);
    }

    public static boolean containsExplain(Set<Provenance> explains, Provenance explain) throws ErrorFatal {
        for(Provenance ex : explains)  {
            if(ex.alphas.size() == explain.alphas.size()) {
                boolean eq = true;
                Iterator<Expr> ai = ex.alphas.iterator();
                Iterator<Expr> bi = explain.alphas.iterator();
                while(ai.hasNext()) {
                    eq &= ai.next().toString().equals(bi.next().toString());
                }
                if(eq) return true;
            }
        }
        return false;
    }

    // Take set of fmlas, break down AND nodes + remove duplicates.
    // Duplicate checking is done by toString(). Kludgey, but can't rely on .equals().
    public static void removeDuplicateConstraints(List<Expr> fmlas) {
        breakApartANDNodes(fmlas);

        Set<String> seenStrings = new HashSet<String>(fmlas.size());
        Set<Expr> toRemove = new HashSet<Expr>();
        for(Expr f : fmlas) {
            if(seenStrings.contains(f.toString()))
                toRemove.add(f);
            seenStrings.add(f.toString());
        }
        fmlas.removeAll(toRemove);                
    }



    public static void breakApartANDNodes(List<Expr> fmlas) {
        Set<Expr> toAdd = new HashSet<Expr>();
        for(Expr f : fmlas) {
            breakANDHelper(f, toAdd);
        }        
        fmlas.clear();
        fmlas.addAll(toAdd);
    }

    private static void breakANDHelper(Expr f, Set<Expr> toAdd) {
        if(f instanceof ExprBinary && ((ExprBinary) f).op.equals(ExprBinary.Op.AND)) {
            breakANDHelper(((ExprBinary) f).left, toAdd);
            breakANDHelper(((ExprBinary) f).right, toAdd);
        } else if(f instanceof ExprList && ((ExprList) f).op.equals(ExprList.Op.AND)) {
            for(Expr subf : ((ExprList) f).args) {
                breakANDHelper(subf, toAdd);
            }
        } else {
            // Base case: add this non-AND formula
            toAdd.add(f);
        }        
    }

    public static Expr desugarDISJOINT(ExprList x) throws Err {    
        // As given by TranslateAlloyToKodkod.visit(ExprList) (implicit case at end)
        // "This says  no(a&b) and no((a+b)&c) and no((a+b+c)&d)..."
        Expr sum = null;
        Expr result = null;
        for(Expr arg : x.args) {
            if(sum == null) sum = arg;
            else {
                Expr sub = sum.intersect(arg).no();            
                if(result == null) result = sub;
                else               result = result.and(sub);
                sum = sum.plus(arg);
            }
        }
        if(result == null) return ExprConstant.TRUE;
        return result;
    }
    
    public static Expr desugarTOTALORDER(ExprList x) throws Err {
        // XXX TN: taken from TranslateAlloyToKodkod.visit(ExprList)
        //     TN: Seems to be an internal type of ExprList not exposed except by ordering-related declarations.
        //     TN: is this how the implicit constraints not included explicitly in the util/ordering library get added?
        if (x.op == ExprList.Op.TOTALORDER) {
            // XXX TN: removed cset calls from args 0, 1, and 2. so may miss stripping multiplicity
            Expr elem = x.args.get(0), first = x.args.get(1), next = x.args.get(2);
            
            // TN: This if looks like an optimization (from the docs on .totalorder and the comments where totalOrderPredicates is used)
            //   TN (later): we had to add a "frame != null" condition to this optimization in the original; see comments there.
            /*if (elem instanceof Relation && first instanceof Relation && next instanceof Relation) {
                Relation lst = frame.addRel("", null, frame.query(true, (Relation)elem, false));
                totalOrderPredicates.add((Relation)elem); totalOrderPredicates.add((Relation)first); totalOrderPredicates.add(lst); totalOrderPredicates.add((Relation)next);
                return k2pos(((Relation)next).totalOrder((Relation)elem, (Relation)first, lst), x);
            }*/
            Expr f1 = elem.in(first.join(next.reflexiveClosure())); // every element is in the total order
            Expr f2 = next.join(first).no(); // first element has no predecessor            
            Decl elemDecl = elem.oneOf("v" + Integer.toString(TranslateAlloyToKodkod.cnt++));
            ExprHasName e = elemDecl.names.get(0);
            Expr f3 = e.equal(first).or(next.join(e).one()); // each element (except the first) has one predecessor
            Expr f4 = e.equal(elem.minus(next.join(elem))).or(e.join(next).one()); // each element (except the last) has one successor
            Expr f5 = e.in(e.join(next.closure())).not(); // there are no cycles
            return f3.and(f4).and(f5).forAll(elemDecl).and(f1).and(f2);
        }
        else throw new ErrorFatal("Called desugarTOTALORDER on non total order expr: "+x);
    }

    public static boolean isNumericExpr(Expr e) {
        if(e instanceof ExprUnary) {
            ExprUnary eu = (ExprUnary) e;
            if(eu.op.equals(ExprUnary.Op.CARDINALITY) ||
               eu.op.equals(ExprUnary.Op.CAST2INT)    ||
               eu.op.equals(ExprUnary.Op.CAST2SIGINT)) {
                return true;
            }                
        } else if (e instanceof ExprConstant) {
            return ((ExprConstant) e).op.equals(ExprConstant.Op.NUMBER);
        }
        
        return false;
    }
    
    // XXX Naive approach: may be incredibly slow since constructing many TupleSets
    public static Set<TupleSet> getNElementSubsets(int bucketSize, TupleSet ub) {
        Set<TupleSet> result = new HashSet<TupleSet>();
    
        //System.out.println("gNES: "+bucketSize+"; "+ub);
        
        // Base case
        if(bucketSize == 0) return result;
        
        for(Tuple pickT : ub) {            
            // if pickT is our bucketSize-th element
            TupleSet smaller = ub.clone();
            smaller.remove(pickT);
            Set<TupleSet> recurResult = getNElementSubsets(bucketSize-1, smaller);
            
            if(recurResult.isEmpty()) {
                TupleSet newts = ub.universe().factory().noneOf(ub.arity());
                newts.add(pickT);
                result.add(newts);
            } else {
                for(TupleSet subset : recurResult) {
                    subset.add(pickT); // mutative!
                    result.add(subset);
                }    
            }            
        }
        
        return result;
    }


    // No longer used. Doesn't accurately represent the semantics of IDEN unless subBounds is all used atoms
    /*
    static TupleSet getIdenFromAtomsUsed(TupleSet subBounds) {
        Set atomsUsed = new HashSet<Object>();
        for(Tuple t : subBounds) {
            for(int ii=0;ii<t.arity();ii++) {
                atomsUsed.add(t.atom(ii));
            }            
        }
        
        TupleSet result = new TupleSet(subBounds.universe(), subBounds.arity());
        for(Object a : atomsUsed) {
            result.add(subBounds.universe().factory().tuple(a, a));
        }
        return result;
    }*/

    static TupleSet buildClosureOfTupleSet(A4Solution soln, TupleSet ts) {
        // For something like Node -> Node this isn't necessary, but suppose we have a more refined upper bound; 
        // upper(R) = {(1,2), (2,3)} ~~ then upper(^R) = {(1,2), (2,3), (1,3)} 
        TupleSet result = new TupleSet(ts.universe(), ts.arity());        
        TupleSet toAdd = new TupleSet(ts.universe(), ts.arity()); 
        result.addAll(ts);
        
        do {
            toAdd.clear(); // prepare for this iteration (don't do at end; will prematurely exit the loop)
            for(Tuple t1 : result) {        // in TC
                for(Tuple t2 : ts) { // extend 
                    Tuple newT = AmalgamVisitorHelper.joinTuple(soln, t1, t2);
                    //debug(" ~join~ result: "+t1+" . "+t2+" = "+newT);
                    if(newT == null) continue; // can't join, ignore                    
                    if(!result.contains(newT))
                        toAdd.add(newT);
                }
            }
            result.addAll(toAdd);            
        } while(toAdd.size() > 0);       
        return result;
    }



}
