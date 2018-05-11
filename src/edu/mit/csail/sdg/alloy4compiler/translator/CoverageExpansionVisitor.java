package edu.mit.csail.sdg.alloy4compiler.translator;

import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.buildSimplePaths;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.desugarQuantifier;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.getQtSingleVar;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.getQtSingleVarExpr;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.joinTuple;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.projectTuple;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.projectTupleRange;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.transposeTuple;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.tuple2Expr;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
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
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;

public class CoverageExpansionVisitor extends VisitReturn<Expr> {
    
    final private A4Solution orig;
    final private Module root;
    boolean currentSign; // polarity
    Tuple currentTupleIfAtomic = null;
    //private Expr contextNumericOther = null;
    private final AmalgamNaiveEvaluator eOrig;
    
    public CoverageExpansionVisitor(Module root, A4Solution ans) {
        this.root = root;
        this.orig = ans;
        this.currentSign = true;
        this.eOrig = new AmalgamNaiveEvaluator(root, orig, true);
    }
    
    boolean shouldNotDescend(Expr x) throws Err {
        Object result = x.accept(eOrig);
        if (result instanceof A4TupleSet || result instanceof Integer) {
            return false;
        }
        Boolean res = (Boolean) result;
        return (currentSign && !res) || (!currentSign && res);
    }
    
    private void mustHaveTupleContext(Expr x) throws Err {
        if(currentTupleIfAtomic == null)
            throw new ErrorFatal("Relational expression had no tuple context: "+x);
    }

    
    @Override
    public Expr visit(ExprBinary x) throws Err {
        if (shouldNotDescend(x)) return null;
        
        switch (x.op) {
        case AND:
        case OR: {
            List<Expr> args = new ArrayList<>(2);
            args.add(x.left);
            args.add(x.right);
            Expr desugared = ExprList.make(x.pos, x.closingBracket, (x.op.equals(ExprBinary.Op.AND) ? ExprList.Op.AND : ExprList.Op.OR), args);
            return desugared.accept(this);
        } case IFF: {
            Expr impl1 = ExprBinary.Op.IMPLIES.make(x.pos, x.closingBracket, x.left, x.right);
            Expr impl2 = ExprBinary.Op.IMPLIES.make(x.pos, x.closingBracket, x.right, x.left);                
            Expr desugared = ExprBinary.Op.AND.make(x.pos, x.closingBracket, impl1, impl2);
            return desugared.accept(this);
        } case IMPLIES: {
            Expr desugared = ExprBinary.Op.OR.make(x.pos, x.closingBracket, x.left.not(), x.right);
            return desugared.accept(this);
        } case IN: {
            TupleSet ub = x.left.accept(new AmalgamUpperBoundVisitor(root, orig));

            boolean isGroundLHS = AmalgamVisitorHelper.isGroundProduct(x.left);
           
            if(isGroundLHS && ub.size() == 1) { 
                // True base case: tuple in EXPR, can't desugar LHS any more
                currentTupleIfAtomic = ub.iterator().next();
                Expr result = x.right.accept(this);
                currentTupleIfAtomic = null;                   
                return result;
            } else if(ub.size() > 0) {
                // Break out LHS of the IN
                
                // If we have something like "R in one X"; desugar to get rid of multiplicity.
                // First we may need to remove heaping spoonfuls of sugar
                
                
                Expr xmult = AmalgamVisitorHelper.isIn(x.left, x.right, true);
                if(xmult != null) {
                    return xmult.accept(this); 
                } else {
                    TupleSet upperBoundInstantiations = x.left.accept(new AmalgamUpperBoundVisitor(root, orig));
                    if(upperBoundInstantiations.size() < 1) 
                        throw new ErrorFatal("DiffEval on some E but E had empty upper bound: "+x.left);

                    List<Expr> subFmlas = new ArrayList<Expr>(); 
                    for(Tuple instantiation : upperBoundInstantiations) {
                        Expr tup = tuple2Expr(orig, instantiation);
                        subFmlas.add(tup.in(x.left).implies(tup.in(x.right)));
                    }

                    Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, subFmlas);                                               
                    return desugared.accept(this);                    
                } // end case where no need to desugar multiplicities in RHS
            } else {
                // XXX: Oak, |ub| = 0, which could happen in alpha, so do not continue recursion
                return x;                    
            }
        } case NOT_IN: {
            Expr desugared = x.left.in(x.right).not();
            return desugared.accept(this);
        } case EQUALS: {
            if(AmalgamVisitorHelper.isNumericExpr(x.left) || AmalgamVisitorHelper.isNumericExpr(x.right)) {
                return x; // TODO: Oak INTIGNORE 
            } else {
                Expr desugared = x.left.in(x.right).and(x.right.in(x.left));
                return desugared.accept(this);                                    
            }
        } case NOT_EQUALS: {
            Expr desugared = x.left.equal(x.right).not();
            return desugared.accept(this);
        } 
        
        // ***************************************
        // Relational binary expressions
        // ***************************************
        
        case PLUS: {
            mustHaveTupleContext(x);
            // desugar as \/       
            Tuple saveTuple = currentTupleIfAtomic;
            Expr desugared1 = tuple2Expr(orig, currentTupleIfAtomic).in(x.left); 
            Expr desugared2 = tuple2Expr(orig, currentTupleIfAtomic).in(x.right);
            currentTupleIfAtomic = null; // back in Boolean context
            Expr result = desugared1.or(desugared2).accept(this); 
            currentTupleIfAtomic = saveTuple; // return to Relational context
            return result;
        } case INTERSECT: {
            mustHaveTupleContext(x);
            // desugar as /\       
            Tuple saveTuple = currentTupleIfAtomic;
            Expr desugared1 = tuple2Expr(orig, currentTupleIfAtomic).in(x.left); 
            Expr desugared2 = tuple2Expr(orig, currentTupleIfAtomic).in(x.right);
            currentTupleIfAtomic = null; // back in Boolean context
            Expr result = desugared1.and(desugared2).accept(this); 
            currentTupleIfAtomic = saveTuple; // return to Relational context
            return result;
        } case DOMAIN: {
            mustHaveTupleContext(x);
            // t in A <: B  means t in B and the first component of t is in A.
            Expr inRight = tuple2Expr(orig, currentTupleIfAtomic).in(x.right);
            Expr inLeftFirst = tuple2Expr(orig, projectTuple(orig, currentTupleIfAtomic, 0)).in(x.left);
            List<Expr> lst = new ArrayList<Expr>(2);
            lst.add(inRight);
            lst.add(inLeftFirst);
            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, lst);                
            return desugared.accept(this);  
        } case RANGE: {
            mustHaveTupleContext(x);
            // t in B :> A  means t in B and the last component of t is in A.
            Expr inLeft = tuple2Expr(orig, currentTupleIfAtomic).in(x.left);
            Expr inRightLast = tuple2Expr(orig, projectTuple(orig, currentTupleIfAtomic, currentTupleIfAtomic.arity()-1)).in(x.right);
            List<Expr> lst = new ArrayList<Expr>(2);
            lst.add(inRightLast);
            lst.add(inLeft);
            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, lst);
            return desugared.accept(this);
        } case JOIN: {
            mustHaveTupleContext(x);

            // Desugar as large disjunction. 
            // t in A.B (A nary, B mary) ~~> \/ [ta, tb in UBs | ta.tb = t] (ta in A /\ tb in B)                                

            TupleSet ubLeft = x.left.accept(new AmalgamUpperBoundVisitor(root, orig));
            TupleSet ubRight = x.right.accept(new AmalgamUpperBoundVisitor(root, orig));
            
            List<Expr> possibilities = new ArrayList<Expr>();
            for(Tuple ta : ubLeft) {
                for(Tuple tb : ubRight) {
                    // Does this pair join into t?
                    if(currentTupleIfAtomic.equals(joinTuple(orig, ta, tb))) // joinTuple returns null if they don't join
                    {
                        Expr exprTA = tuple2Expr(orig, ta);
                        Expr exprTB = tuple2Expr(orig, tb);
                        // If exprTA is exactly equal to x.left, don't produce AND[Node$0 in Node$0, ...]
                        // Beware because there may be a NO-OP unary operator wrapping the ExprVar.
                        Expr possibility;
                        Expr deNOPLeft = x.left.deNOP();
                        if(deNOPLeft.equals(exprTA)) {                                
                            possibility = exprTB.in(x.right);
                        } else {                                
                            possibility = exprTA.in(x.left).and(exprTB.in(x.right));
                        }
                        possibilities.add(possibility);
                    }
                }                    
            }

            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, possibilities);
            Tuple saveTuple = currentTupleIfAtomic;
            currentTupleIfAtomic = null;
            Expr result = desugared.accept(this);
            currentTupleIfAtomic = saveTuple;
            return result;
        } case MINUS: {
            mustHaveTupleContext(x);
            // in LHS but not in RHS: desugar as /\ (with negation on RHS)
            Tuple saveTuple = currentTupleIfAtomic;
            Expr desugared1 = tuple2Expr(orig, currentTupleIfAtomic).in(x.left); 
            Expr desugared2 = tuple2Expr(orig, currentTupleIfAtomic).in(x.right).not();
            currentTupleIfAtomic = null; // back in Boolean context
            Expr result = desugared1.and(desugared2).accept(this); 
            currentTupleIfAtomic = saveTuple; // return to Relational context
            return result;
        } case PLUSPLUS: {
            mustHaveTupleContext(x);
            // Relational override with tuple context on LHS: desugar as OR of 2 cases.
            //  in RHS
            //  in LHS, and first column is NOT in RHS (with any other columns)
            Expr inRight = tuple2Expr(orig, currentTupleIfAtomic).in(x.right);
            Expr inLeft = tuple2Expr(orig, currentTupleIfAtomic).in(x.left);

            Expr firstColumnTuple = tuple2Expr(orig, projectTuple(orig, currentTupleIfAtomic, 0));
            Expr firstColumnRight = x.right;
            while(firstColumnRight.type().arity() > 1) {
                // keep joining univ onto right until we have a unary relation: the leftmost column
                firstColumnRight = firstColumnRight.join(Sig.UNIV);
            }
            Expr firstInRight = firstColumnTuple.in(firstColumnRight);
            Expr inLeftFirstNotInRight = inLeft.and(firstInRight.not()); 
            //System.err.println("Amalgam DEBUG: Desugaring ++: "+x+" ;  inLeftFirstNotInRight: "+inLeftFirstNotInRight);

            // XXX TN: Please test this (I could get a provenance, but may need to do in GroundVisitor to actually call this?)
            // XXX TN: I also suspect that some other spec issues may be missing disj keyword in quantification. 

            List<Expr> lst = new ArrayList<Expr>(2);
            lst.add(inRight);
            lst.add(inLeftFirstNotInRight);
            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, lst);
            return desugared.accept(this);
        } case ARROW: {
            mustHaveTupleContext(x);
            // RHS: A->B with tuple context for LHS: desugar as AND of 2 subtuple membership exprs.

            Tuple leftTupleContext = projectTupleRange(orig, currentTupleIfAtomic, 0, x.left.type().arity());
            Tuple rightTupleContext = projectTupleRange(orig, currentTupleIfAtomic, x.left.type().arity(), x.right.type().arity()); 
            List<Expr> fmlas = new ArrayList<Expr>(2);
            fmlas.add(tuple2Expr(orig, leftTupleContext).in(x.left));
            fmlas.add(tuple2Expr(orig, rightTupleContext).in(x.right));
            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, fmlas);
            return desugared.accept(this);
        } 
        
        case ANY_ARROW_LONE:
        case ANY_ARROW_ONE:
        case ANY_ARROW_SOME:
        case LONE_ARROW_ANY:
        case LONE_ARROW_LONE:
        case LONE_ARROW_ONE:
        case LONE_ARROW_SOME:
        case ONE_ARROW_ANY:
        case ONE_ARROW_LONE:
        case ONE_ARROW_ONE:
        case ONE_ARROW_SOME:
        case SOME_ARROW_ANY:
        case SOME_ARROW_LONE:
        case SOME_ARROW_ONE:
        case SOME_ARROW_SOME:
            throw new ErrorFatal("Amalgam does not yet desugar complex-multiplicity arrow operator: "+x.op);
            
        case NOT_GT: return x.left.gt(x.right).not().accept(this);
        case NOT_LT: return x.left.lt(x.right).not().accept(this);
        case NOT_GTE: return x.left.gte(x.right).not().accept(this);
        case NOT_LTE: return x.left.lte(x.right).not().accept(this);
        
        case GT:
        case LT:
        case LTE:
        case GTE:
            return x; // TODO: Oak INTIGNORE
            
        case DIV:
        case REM:
        case MUL:
        case IPLUS:
        case IMINUS:
        case SHA:
        case SHL:
        case SHR:
            throw new ErrorFatal("Numeric binary operator "+x.op+" is unsupported in amalgam (diff eval visitor): "+x);
            
        default: throw new ErrorFatal("Unsupported binary op: "+x);
        }
    }

    @Override
    public Expr visit(ExprList x) throws Err {
        if (shouldNotDescend(x)) return null;
        switch (x.op) {
        case TOTALORDER: {
            return AmalgamVisitorHelper.desugarTOTALORDER(x).accept(this);
        }
        case AND:
        case OR: {
            List<Expr> args = new ArrayList<>(x.args.size());
            for(Expr e : x.args) {
                Expr added = e.accept(this);
                if (added != null) args.add(added);
            }
            return ExprList.make(x.pos, x.closingBracket, x.op, args);
        }
        default: throw new ErrorFatal("Unsupported op: "+x);
        }
    }

    @Override
    public Expr visit(ExprCall x) throws Err {
        if (shouldNotDescend(x)) return null;
        return AmalgamVisitorHelper.resolveExprCall(x).accept(this);
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {
        return x;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {
        if (shouldNotDescend(x)) return null;

        Expr desugared = x.cond.and(x.left).or(x.cond.not().and(x.right));                        
        return desugared.accept(this);
    }

    @Override
    public Expr visit(ExprLet x) throws Err {
        if (shouldNotDescend(x)) return null;
        Expr desugared = x.sub.accept(new AmalgamSubstituteVisitor(x.var, x.expr, false));
        return desugared.accept(this);
    }

    @Override
    public Expr visit(ExprQt x) throws Err {
        if (shouldNotDescend(x)) return null;
        
        switch (x.op) {
        case ALL:
        case SOME:
        case LONE:
        case ONE:
        case NO: {
            Expr desugaredPre = desugarQuantifier(x);
            if(!(desugaredPre instanceof ExprQt)) // 2nd branch occurs if we've desugared "one" 
                return desugaredPre.accept(this);
            x = (ExprQt) desugaredPre;
            
            // Quantified: have *many* potential subexpressions w/ quantified var instantiated

            // Alloy's eval function just translates to Kodkod and then uses Kodkod's eval function
            // We need to instantiate *Alloy* expressions. 
            // Take advantage of the fact that Alloy creates a sig for each atom; build each into an expr and substitute.
            
            ///////////////////
            // all/some v: T | F(x) 
            ///////////////////

            // Get v and T
            ExprHasName v = getQtSingleVar(x);
            Expr T = getQtSingleVarExpr(x);                
            // Get set of potential instantiations
            TupleSet upperBoundInstantiations = T.accept(new AmalgamUpperBoundVisitor(root, orig));        
            
            // all v: T | F(x) 
            //    ~~> T(t1) => F(t1) /\ ...
            // some v: T | F(x) 
            //    ~~> T(t1) /\ F(t1) \/ ...

            List<Expr> subExprs = new ArrayList<Expr>();        

            for(Tuple tup : upperBoundInstantiations) {           
                // Substitute <instantation> for <v>
                //debug("visitQuantifier Calling tuple2Expr on "+tup);
                Expr instantiation = tuple2Expr(orig, tup);
                //debug("visitQuantifier SUBSTITUTING: "+v+" ~> "+instantiation+" (was tuple: "+tup+")...");            
                Expr substituted = x.sub.accept(new AmalgamSubstituteVisitor(v, instantiation, false));                  

                // Just desugar: pay no attention to whether the sign is pos or neg at the moment.
                Expr qinst;
                if(x.op.equals(ExprQt.Op.ALL)) 
                    qinst = instantiation.in(T).not().or(substituted);
                else if(x.op.equals(ExprQt.Op.SOME))
                    qinst = instantiation.in(T).and(substituted);
                else
                    throw new ErrorFatal("Unknown quantifier type (after desugaring): "+x.op);

                // (Remember, all/some here is in context of sign)
                // If "all", this qinst must be true in orig. SOME qinst is false in flipped.
                // If "some", this qinst  must be false in flipped. SOME qinst is true in orig.

                subExprs.add(qinst);
            }

            Expr desugared = ExprList.make(x.pos, x.closingBracket, (x.op.equals(ExprQt.Op.ALL) ? ExprList.Op.AND : ExprList.Op.OR), subExprs);        
            return desugared.accept(this);
        } case COMPREHENSION: {
            return AmalgamVisitorHelper.desugarComprehension(orig, x, currentTupleIfAtomic).accept(this);
        } case SUM: {
            throw new ErrorFatal("sum numeric operator not yet supported by Amalgam");
        } default:
            throw new ErrorFatal("unexpected operator in ExprQt visit: "+x);
        }
    }

    //private ExprUnary lastNOOP = null; 

    @Override
    public Expr visit(ExprUnary x) throws Err {
        if (shouldNotDescend(x)) return null;
        
        switch (x.op) {
        case NOOP: {
            //lastNOOP = x;
            return x.sub.accept(this);
        } 
        
        case CAST2INT:
        case CAST2SIGINT:
            return x.sub.accept(this);
            
        case CARDINALITY: {
            return x; // TODO: Oak INTIGNORE
        } case NOT: {
            currentSign = !currentSign;
            Expr result = ExprUnary.Op.NOT.make(x.pos, x.sub.accept(this));
            currentSign = !currentSign;
            return result;
        } case SOME: {
            TupleSet upperBoundInstantiations = x.sub.accept(new AmalgamUpperBoundVisitor(root, orig));
            if(upperBoundInstantiations.size() < 1) 
                return x; // TODO

            List<Expr> subFmlas = new ArrayList<Expr>(); 
            for(Tuple instantiation : upperBoundInstantiations) {
                Expr tup = tuple2Expr(orig, instantiation);
                subFmlas.add(tup.in(x.sub));
            }

            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, subFmlas);                                               
            return desugared.accept(this);
        } case LONE: {
            return x.sub.one().or(x.sub.no()).accept(this);
        } case ONE: {
            TupleSet upperBoundInstantiations = x.sub.accept(new AmalgamUpperBoundVisitor(root, orig));
            if(upperBoundInstantiations.size() < 1) 
                //throw new ErrorFatal("DiffEval on some E but E had empty upper bound");
                return x;

            List<Expr> subFmlas = new ArrayList<Expr>(); 
            for(Tuple instantiation : upperBoundInstantiations) {
                Expr tup = tuple2Expr(orig, instantiation);
                List<Expr> uniques = new ArrayList<Expr>();

                // ...and none of the other tuples are in the expression
                for(Tuple other : upperBoundInstantiations) {
                    if(other.equals(instantiation)) continue;
                    Expr tup2 = tuple2Expr(orig, other);
                    Expr unique = tup2.in(x.sub).not();
                    uniques.add(unique);
                }                    
                Expr uniqueness = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, uniques);                     
                subFmlas.add(tup.in(x.sub).and(uniqueness));
            }

            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, subFmlas);                                               
            return desugared.accept(this);
        } case NO: {
            Expr desugared = x.sub.some().not();
            return desugared.accept(this);
        } 
        
        // *********************************
        // Relational unary operators
        // *********************************
        
        case SETOF: {
            return x.sub.accept(this);
        } case CLOSURE: {
         // Desugar as (potentially massive) disjunction. Enumerate all paths in upper bound.
            mustHaveTupleContext(x);

            if(currentTupleIfAtomic.arity() != 2) 
                throw new ErrorFatal("Tried to compute closure with non-binary tuple context: "+currentTupleIfAtomic);                
            Object source = currentTupleIfAtomic.atom(0);
            Object destination = currentTupleIfAtomic.atom(1);

            TupleSet ub = x.sub.accept(new AmalgamUpperBoundVisitor(root, orig));

            // For <s,d> to be in ^sub, one of the possible paths has to be there.
            Set<List<Object>> spaths = buildSimplePaths(source, destination, ub, new HashSet<Object>());


            List<Expr> possibilities = new ArrayList<Expr>();
            for(List<Object> apath : spaths) {
                Expr possibility = null;
                for(int ii=0;ii<apath.size()-1;ii++) {
                    // for each edge taken in this path
                    Tuple thop = orig.getFactory().tuple(apath.get(ii), apath.get(ii+1));                        
                    Expr ehop = tuple2Expr(orig, thop);                        
                    Expr hopexists = ehop.in(x.sub);
                    if(possibility == null) {
                        possibility = hopexists;
                    } else {
                        possibility = possibility.and(hopexists);
                    }                        
                }
                possibilities.add(possibility);                                   
            }

            // No need for context; we're shifting up to boolean again
            Tuple saveTuple = currentTupleIfAtomic;
            currentTupleIfAtomic = null;
            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, possibilities);
            Expr result = desugared.accept(this);
            currentTupleIfAtomic = saveTuple;
            return result;
        } case RCLOSURE: {
            mustHaveTupleContext(x);
            // sugar
            Expr desugared = ExprConstant.IDEN.plus(x.sub.closure());
            return desugared.accept(this);
        } case TRANSPOSE: {
            mustHaveTupleContext(x);
            // flip the context tuple
            Tuple saveTuple = currentTupleIfAtomic;
            currentTupleIfAtomic = transposeTuple(orig, currentTupleIfAtomic);
            Expr result = x.sub.accept(this);
            currentTupleIfAtomic = saveTuple;
            return result;
        } default: throw new ErrorFatal("Unsupported unary operator: "+x.op+" in "+x);
        }
    }

    @Override
    public Expr visit(ExprVar x) throws Err {
        return x;
    }

    @Override
    public Expr visit(Sig x) throws Err {
        if (x instanceof PrimSig && x.needToDesugar && !x.equals(Sig.UNIV) && !x.equals(Sig.NONE) && !x.equals(Sig.STRING) &&
                !x.equals(Sig.SEQIDX) && !x.equals(Sig.SIGINT)) {
            x.needToDesugar = false;
            Expr accUnion = null;
            boolean first = true;
            for (PrimSig desc : ((PrimSig) x).descendents()) {
                if (first) {
                    first = false;
                    accUnion = desc;
                    continue;
                }
                accUnion = accUnion.plus(desc);
            }
            if (accUnion == null) {
                return x;
            }
            Expr result = accUnion.plus(x.minus(accUnion)).accept(this);
            x.needToDesugar = true;
            return result;
        }
        // TODO: Oak
        return x;
    }

    @Override
    public Expr visit(Field x) throws Err {
        return x;
    }
}
