package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
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
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTree.Annotation;
import gnu.trove.map.hash.TCustomHashMap;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary.Op;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.*;

public class AmalgamEvalVisitor extends VisitReturn<ProvenanceTree> {                                    
    final A4Solution orig;
    final A4Solution flipped;
    final Module root;    
    final Expr flipRel;
    final Tuple flipTup;
    
    /** Record what each subformula produced binds. This avoids having to do fancier desugaring in the quantified-expr case. */    
    final Map<Expr, Pair<ExprHasName, Object>> qBindings = new HashMap<Expr, Pair<ExprHasName, Object>>();
    /** Record the bindings taken in current provenance branch. Built from qBindings. Remember to pop as well as push. */
    final Map<ExprHasName, Object> provBindings = new HashMap<ExprHasName, Object>();
        
    /**
     * After visit pattern complete, contains all subexpressions of the original fmla
     * that were visited. Will not contain subexpressions that appear only within
     * expressions that evaluate to the same value in orig vs. flipped.
     */
    //public Map<Expr, Boolean> diffCache = new HashMap<Expr, Boolean>(1000);
    public Map<Expr, Boolean> diffCache = new TCustomHashMap<Expr, Boolean>(AmalgamVisitorHelper.strat, 1000);
    
    /**
     * After visit pattern complete, contains all subexpressions of the original fmla that 
     *   (1) evaluate to different values in orig vs. flipped; and
     *   (2) do not only appear within superexpressions that evaluate to the same value in orig vs. flipped.
     *   upper
     *   For instance, if we pass "e1 in e2", which produces true in both instances, this field will not
     *   contain e1 even if e1 is different in one of the instances.
     */
    //public Set<Expr> differingSubExpressions = new HashSet<Expr>();

    private boolean currentSign = true;
    private Tuple currentTupleIfAtomic = null;

    private Expr contextNumericOther = null;
        
    public int numSanityChecks = 0;
    
    private final AmalgamNaiveEvaluator eOrig;
    private final AmalgamNaiveEvaluator eFlip;
    
    public AmalgamEvalVisitor(Module root, A4Solution orig, A4Solution flipped, 
                                           Expr flipRel, A4Tuple a4flipTup) throws Err {
        this.orig = orig;
        this.flipped = flipped;
        this.root = root; 
        this.flipRel = flipRel;
        this.flipTup = a4flipTup.getOriginalTuple();                       
        
        eOrig = new AmalgamNaiveEvaluator(root, orig, true);
        eFlip = new AmalgamNaiveEvaluator(root, flipped, true);
        
    }

    public void debug(String msg, Expr x) {
        // If this method accepted a String only, and the caller passed something like 
        // "my message: "+x, where x is an Expr, Java would call x.toString and concatenate
        // even if this debug flag were false.
        if(AmalgamVisitorHelper.debugDiffEval) System.err.println("########## Amalgam EVAL Visitor Debug (sign="+currentSign+"; tuple="+currentTupleIfAtomic+") "+msg+": "+x);
    }

    /**
     * If debug mode is on, do a sanity check that x differs between the two models.
     * If debug mode is off, just return true and remember that we've visited this expression.
     * @param x
     * @return
     * @throws Err
     */
    public boolean diffResultsHelperSanityCheck(Expr x) throws Err {
        numSanityChecks++;
        if(AmalgamVisitorHelper.sanityCheck)
            return diffResultsHelper(x);
        else {
            // DO NOT add to diffCache here; that is a cache for true differencing.
            return true;
        }
    }
        
    // TODO: move cache up; just testing for now
    private Object evaluate(A4Solution aSol, Expr x) throws Err {   
        if(aSol == orig)    return x.accept(eOrig);
        if(aSol == flipped) return x.accept(eFlip);
        throw new ErrorFatal("EvalVisitor tried to evaluate on an unknown solution!");
    }
    
    /**
     * Return whether the expression evaluates differently in the two models.
     * (Note that this function is called for more than just sanity-checking!)
     * @param x
     * @return
     * @throws Err
     */
    public boolean diffResultsHelper(Expr x) throws Err {
        if(diffCache.containsKey(x))
        {
            return diffCache.get(x);
        }

        Object origAnswer = evaluate(orig, x);
        Object flipAnswer = evaluate(flipped, x);
        boolean result;

      //  System.err.println("diffResultsHelper: "+x+"; "+origAnswer+"; "+flipAnswer+"; "+origAnswer.getClass()+" "+flipAnswer.getClass());
        
        if(origAnswer instanceof A4TupleSet && flipAnswer instanceof A4TupleSet) {
            // May be a set, or may be a singleton-set containing an integer
            A4TupleSet origTuples = (A4TupleSet) origAnswer;
            A4TupleSet flipTuples = (A4TupleSet) flipAnswer;
            result = !origTuples.equalValues(flipTuples);            
        } else {                   
            result = !origAnswer.equals(flipAnswer); // Boolean
        }

        //if(result) {
        //    debug("  Expression differed: "+x+" :: "+origAnswer+" ; "+flipAnswer);            
        //}

        diffCache.put(x, result);
        return result;
    }

    @Override
    public ProvenanceTree visit(ExprBinary x) throws Err {
        debug("Visiting ExprBinary (op="+x.op+") expression ", x);
        boolean diff = diffResultsHelperSanityCheck(x);            
        if(diff) 
        {                    
            //List<ProvenanceTree> subs = new ArrayList<ProvenanceTree>();

            // ***************************************
            // Boolean binary expressions
            // ***************************************

            if(x.op.equals(ExprBinary.Op.AND) || x.op.equals(ExprBinary.Op.OR)) {
                // sugar
                List<Expr> args = new ArrayList<Expr>(2);
                args.add(x.left);
                args.add(x.right);
                Expr desugared = ExprList.make(x.pos, x.closingBracket, (x.op.equals(ExprBinary.Op.AND) ? ExprList.Op.AND : ExprList.Op.OR), args);
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
            }

            else if(x.op.equals(ExprBinary.Op.IFF)) {
                // sugar
                
                // old sugar: leads to lower quality provenances---larger alphas because large or branches
                //Expr case1 = ExprBinary.Op.AND.make(x.pos, x.closingBracket, x.left, x.right);
                //Expr case2 = ExprBinary.Op.AND.make(x.pos, x.closingBracket, x.left.not(), x.right.not());                
                //Expr desugared = ExprBinary.Op.OR.make(x.pos, x.closingBracket, case1, case2);
                
                // TN June 6 better sugar: smaller or branches
                // TODO confirm this is ok!
                // 
                Expr impl1 = ExprBinary.Op.IMPLIES.make(x.pos, x.closingBracket, x.left, x.right);
                Expr impl2 = ExprBinary.Op.IMPLIES.make(x.pos, x.closingBracket, x.right, x.left);                
                Expr desugared = ExprBinary.Op.AND.make(x.pos, x.closingBracket, impl1, impl2);
                
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
            }

            else if(x.op.equals(ExprBinary.Op.IMPLIES)) {
                // sugar
                Expr desugared = ExprBinary.Op.OR.make(x.pos, x.closingBracket, x.left.not(), x.right);
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
            }

            // ***************************************
            // R1 in R2: desugaring case
            // tup in R: base Boolean case
            // ***************************************

            else if(x.op.equals(ExprBinary.Op.IN)) {
                // The two instances share bounds, so it doesn't matter which is passed in here. 
                TupleSet ub = x.left.accept(new AmalgamUpperBoundVisitor(root, orig));

                boolean isGroundLHS = AmalgamVisitorHelper.isGroundProduct(x.left);
//                debug("IN formula: "+x+" ~~ ub(left)="+ub+" isGroundLHS="+isGroundLHS);

                if(isGroundLHS && ub.size() == 1) { 
                    // True base case: tuple in EXPR, can't desugar LHS any more
                    debug("Base case IN formula ", x);
                    currentTupleIfAtomic = ub.iterator().next();
                    ProvenanceTree result = x.right.accept(this);
                    currentTupleIfAtomic = null;                   
                    return result.annotate(new ProvenanceTree.PAAtomicIN());
                } else if(ub.size() > 0) {
                    // Break out LHS of the IN
                    
                    debug("Complex IN formula; calling isIn on ", x);
                    // If we have something like "R in one X"; desugar to get rid of multiplicity.
                    // First we may need to remove heaping spoonfuls of sugar
                    Expr xmult = AmalgamVisitorHelper.isIn(x.left, x.right,true);
                    if(xmult != null) {
                        return xmult.accept(this).annotate(new ProvenanceTree.PADesugarMultiplicityInIN()); 
                    } else {
                        debug("Complex IN formula (should see no multiplicity!); desugaring post isIn call ", x);

                        List<ProvenanceTree> casesEachTuple = new ArrayList<ProvenanceTree>();       

                        // because we are optimizing and not fully desugaring, if this is analogous to an or, we need to keep context
                        Set<Expr> contextForSuccess = new HashSet<Expr>();
                        
                        for(Tuple tup : ub) {
                            // To make the fmla TRUE, for each t, ~(t in left) \/ t in right must hold.
                            Expr tupExpr = AmalgamVisitorHelper.tuple2Expr(orig, tup);
                            
                            if(currentSign) {
                                // True in orig, false in flipped
                                // Failure is existential (we can ignore non-responsible conjuncts)
                                //    and combine results of recurring on these w/ POR
                                boolean inLeft = (Boolean) evaluate(flipped, tupExpr.in(x.left)); 
                                boolean inRight = (Boolean) evaluate(flipped, tupExpr.in(x.right));  
                                //debug(" IN tuple: "+tupExpr+": inLeft="+inLeft+"; inRight="+inRight);
                                if(inLeft && !inRight) {                        
                                    // Recur on the implication for this tuple (left => right; !left or right); find why is it failing:
                                    Expr groundLeftNot = tupExpr.in(x.left).not();
                                    Expr groundRight = tupExpr.in(x.right);                                    
                                    List<Expr> lst = new ArrayList<Expr>(2);
                                    lst.add(groundLeftNot); lst.add(groundRight);
                                    Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, lst);
                                    casesEachTuple.add(desugared.accept(this)); // why did this become false?                                              
                                }                       
                            } else {
                                // False in orig, true in flipped
                                // Success is universal: gather non-changing conjuncts as context
                                //   and combine results of recurring on changing conjuncts w/ PAND
                                Expr groundLeftNot = tupExpr.in(x.left).not();
                                Expr groundRight = tupExpr.in(x.right);    
                                List<Expr> lst = new ArrayList<Expr>(2);
                                lst.add(groundLeftNot); lst.add(groundRight);
                                Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, lst);
                                if(!diffResultsHelper(desugared)) contextForSuccess.add(desugared); // new alpha-no difference
                                else casesEachTuple.add(desugared.accept(this)); // why did this become true?                       
                            }
                            
                            
                        } // end loop for each tuple in UB
                        // If this is a sudden failure, POR (any subtree justifies)
                        ProvenanceTree result;
                        if(currentSign)
                             result = ProvenanceNode.construct(ProvenanceNode.Op.POR, x, currentSign, casesEachTuple);
                        // If this is a sudden success, PAND (all failing subtrees together, plus non-differing context, justify)
                        else {
                            for(Expr context : contextForSuccess) {
                                casesEachTuple.add(new ProvenanceLeaf(context));
                            }                           
                            result = ProvenanceNode.construct(ProvenanceNode.Op.PAND, x, currentSign, casesEachTuple);                                        
                        }
                        //debug("  ~~~  IN context ("+x+") produced provenance tree: "+result+"; cases.size()="+casesEachTuple.size());
                        return result.annotate(new ProvenanceTree.PADesugarBinary(x.op));
                    } // end case where no need to desugar multiplicities in RHS
                } else {                    
                    throw new ErrorFatal("Diff Eval Encountered an empty LHS upper-bound tuple set (should result in no difference, so should not hit this case) when processing: "+x);                    
                }
            }
            else if(x.op.equals(ExprBinary.Op.NOT_IN)) {
                // Just sugar for (Boolean) not x in y.
                Expr desugared = x.left.in(x.right).not();
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
            }
            else if(x.op.equals(ExprBinary.Op.EQUALS)) {
                // This could be either numeric or set equals. Find out which.
                if(AmalgamVisitorHelper.isNumericExpr(x.left) || AmalgamVisitorHelper.isNumericExpr(x.right))
                {
                    return buildNumericBinaryFormula(x).annotate(new ProvenanceTree.PADesugarBinary(x.op)); 
                } else {
                    // desugar as 2 ins:
                    Expr desugared = x.left.in(x.right).and(x.right.in(x.left));
                    return desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));                                    
                }
            }
            else if(x.op.equals(ExprBinary.Op.NOT_EQUALS)) {
                // desugar
                Expr desugared = x.left.equal(x.right).not();
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));                
            }

            // ***************************************
            // Relational binary expressions
            // ***************************************

            // TODO: sign awareness
            // TODO: duplicate code when desugaring these...

            else if(x.op.equals(ExprBinary.Op.PLUS)) {
                mustHaveTupleContext(x);
                // desugar as \/       
                Tuple saveTuple = currentTupleIfAtomic;
                Expr desugared1 = tuple2Expr(orig, currentTupleIfAtomic).in(x.left); 
                Expr desugared2 = tuple2Expr(orig, currentTupleIfAtomic).in(x.right);
                currentTupleIfAtomic = null; // back in Boolean context
                ProvenanceTree result = desugared1.or(desugared2).accept(this); 
                currentTupleIfAtomic = saveTuple; // return to Relational context
                return result.annotate(new ProvenanceTree.PADesugarBinary(x.op));
            }
            else if(x.op.equals(ExprBinary.Op.INTERSECT)) {
                mustHaveTupleContext(x);
                // desugar as /\       
                Tuple saveTuple = currentTupleIfAtomic;
                Expr desugared1 = tuple2Expr(orig, currentTupleIfAtomic).in(x.left); 
                Expr desugared2 = tuple2Expr(orig, currentTupleIfAtomic).in(x.right);
                currentTupleIfAtomic = null; // back in Boolean context
                ProvenanceTree result = desugared1.and(desugared2).accept(this); 
                currentTupleIfAtomic = saveTuple; // return to Relational context
                return result.annotate(new ProvenanceTree.PADesugarBinary(x.op));

            }
            else if(x.op.equals(ExprBinary.Op.DOMAIN)) {                
                mustHaveTupleContext(x);
                // t in A <: B  means t in B and the first component of t is in A.
                Expr inRight = tuple2Expr(orig, currentTupleIfAtomic).in(x.right);
                Expr inLeftFirst = tuple2Expr(orig, projectTuple(orig, currentTupleIfAtomic, 0)).in(x.left);
                List<Expr> lst = new ArrayList<Expr>(2);
                lst.add(inRight);
                lst.add(inLeftFirst);
                Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, lst);                
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
            }
            else if(x.op.equals(ExprBinary.Op.RANGE)) {
                mustHaveTupleContext(x);
                // t in B :> A  means t in B and the last component of t is in A.
                Expr inLeft = tuple2Expr(orig, currentTupleIfAtomic).in(x.left);
                Expr inRightLast = tuple2Expr(orig, projectTuple(orig, currentTupleIfAtomic, currentTupleIfAtomic.arity()-1)).in(x.right);
                List<Expr> lst = new ArrayList<Expr>(2);
                lst.add(inRightLast);
                lst.add(inLeft);
                Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, lst);
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
            }
            else if(x.op.equals(ExprBinary.Op.JOIN)) {
                mustHaveTupleContext(x);

                // Desugar as large disjunction. 
                // t in A.B (A nary, B mary) ~~> \/ [ta, tb in UBs | ta.tb = t] (ta in A /\ tb in B)                                

                TupleSet ubLeft = x.left.accept(new AmalgamUpperBoundVisitor(root, orig));
                TupleSet ubRight = x.right.accept(new AmalgamUpperBoundVisitor(root, orig));

                //debug("JOIN: ubLeft: "+ubLeft);
                //debug("JOIN: ubRight: "+ubRight);
                
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
                ProvenanceTree result = desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
                currentTupleIfAtomic = saveTuple;
                return result;
            }
            else if(x.op.equals(ExprBinary.Op.MINUS)) {
                mustHaveTupleContext(x);
                // in LHS but not in RHS: desugar as /\ (with negation on RHS)
                Tuple saveTuple = currentTupleIfAtomic;
                Expr desugared1 = tuple2Expr(orig, currentTupleIfAtomic).in(x.left); 
                Expr desugared2 = tuple2Expr(orig, currentTupleIfAtomic).in(x.right).not();
                currentTupleIfAtomic = null; // back in Boolean context
                ProvenanceTree result = desugared1.and(desugared2).accept(this); 
                currentTupleIfAtomic = saveTuple; // return to Relational context
                return result.annotate(new ProvenanceTree.PADesugarBinary(x.op));
            }
            else if(x.op.equals(ExprBinary.Op.PLUSPLUS)) {
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
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
            }
            else if(x.op.equals(ExprBinary.Op.ARROW)) {
                mustHaveTupleContext(x);
                // RHS: A->B with tuple context for LHS: desugar as AND of 2 subtuple membership exprs.

                Tuple leftTupleContext = projectTupleRange(orig, currentTupleIfAtomic, 0, x.left.type().arity());
                Tuple rightTupleContext = projectTupleRange(orig, currentTupleIfAtomic, x.left.type().arity(), x.right.type().arity()); 
                List<Expr> fmlas = new ArrayList<Expr>(2);
                fmlas.add(tuple2Expr(orig, leftTupleContext).in(x.left));
                fmlas.add(tuple2Expr(orig, rightTupleContext).in(x.right));
                Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, fmlas);
                //debug("Product expression "+x+" desugared to "+desugared);
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));                

            } else if(x.op.equals(ExprBinary.Op.ANY_ARROW_LONE) ||
                    x.op.equals(ExprBinary.Op.ANY_ARROW_ONE) ||
                    x.op.equals(ExprBinary.Op.ANY_ARROW_SOME) ||
                    x.op.equals(ExprBinary.Op.LONE_ARROW_ANY) ||
                    x.op.equals(ExprBinary.Op.LONE_ARROW_LONE) ||
                    x.op.equals(ExprBinary.Op.LONE_ARROW_ONE) ||
                    x.op.equals(ExprBinary.Op.LONE_ARROW_SOME) ||
                    x.op.equals(ExprBinary.Op.ONE_ARROW_ANY) ||
                    x.op.equals(ExprBinary.Op.ONE_ARROW_LONE) ||
                    x.op.equals(ExprBinary.Op.ONE_ARROW_ONE) ||
                    x.op.equals(ExprBinary.Op.ONE_ARROW_SOME) ||               
                    x.op.equals(ExprBinary.Op.SOME_ARROW_ANY) ||
                    x.op.equals(ExprBinary.Op.SOME_ARROW_LONE) ||
                    x.op.equals(ExprBinary.Op.SOME_ARROW_ONE) ||
                    x.op.equals(ExprBinary.Op.SOME_ARROW_SOME)) {
                // Special error message reminding that these are sugar. Could be desugared, but not yet.
                throw new ErrorFatal("Amalgam does not yet desugar complex-multiplicity arrow operator: "+x.op);
                
            } else if(x.op.equals(ExprBinary.Op.NOT_GT)) {
                return x.left.gt(x.right).not().accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
            } else if(x.op.equals(ExprBinary.Op.NOT_LT)) {
                return x.left.lt(x.right).not().accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
            } else if(x.op.equals(ExprBinary.Op.NOT_GTE)) {
                return x.left.gte(x.right).not().accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));
            } else if(x.op.equals(ExprBinary.Op.NOT_LTE)) {
                return x.left.lte(x.right).not().accept(this).annotate(new ProvenanceTree.PADesugarBinary(x.op));                
            }  else if(x.op.equals(ExprBinary.Op.GT) ||
                    x.op.equals(ExprBinary.Op.LT) ||
                    x.op.equals(ExprBinary.Op.LTE) ||
                    x.op.equals(ExprBinary.Op.GTE)) {
                // Supported numeric binary operators. Desugar as disjunction of equals.
                return buildNumericBinaryFormula(x).annotate(new ProvenanceTree.PADesugarBinary(x.op));                
            } else if(x.op.equals(ExprBinary.Op.DIV) ||
                    x.op.equals(ExprBinary.Op.REM) ||
                    x.op.equals(ExprBinary.Op.MUL) ||                    
                    x.op.equals(ExprBinary.Op.IPLUS) ||
                    x.op.equals(ExprBinary.Op.IMINUS) ||
                    x.op.equals(ExprBinary.Op.SHA) ||
                    x.op.equals(ExprBinary.Op.SHL) ||
                    x.op.equals(ExprBinary.Op.SHR)) {
                // Special error message the indicates this failure is due to numerics
                throw new ErrorFatal("Numeric binary operator "+x.op+" is unsupported in amalgam (diff eval visitor): "+x);
            }                       
            else                
                throw new ErrorFatal("Unsupported binary op: "+x);

        } else {
            throw new ErrorFatal("Called Amalgam diff eval on ExprBinary that didn't change value: "+x);
        }
        
    }

    private ProvenanceTree buildNumericBinaryFormula(ExprBinary x) throws Err {
        // numeric expressions. set context:        
        boolean diffLeft = diffResultsHelper(x.left);
        boolean diffRight = diffResultsHelper(x.right);
        // build numeric formula (in bnbfB) *and* add the alpha that sets the invariant side constant
        if(diffLeft && !diffRight) {
            contextNumericOther = x.right;       
            return addFixedEquality(buildNumericBinaryFormulaB(x, x.left, x.op), x).annotate(new ProvenanceTree.PAFixedEquality(diffLeft, diffRight));                        
        } else if(diffRight && !diffLeft) {
            contextNumericOther = x.left;
            ExprBinary.Op flippedOp = flipBinaryOperator(x.op);            
            return addFixedEquality(buildNumericBinaryFormulaB(x, x.right, flippedOp), x).annotate(new ProvenanceTree.PAFixedEquality(diffLeft, diffRight));
        } else
        {
            throw new ErrorFatal("Both sides of numeric expression differed when flipping literal: "+x);
        }                    
    }

    public static Op flipBinaryOperator(Op op) {
        // DO NOT CONFUSE with negateBinaryOperator
        //  equals is symmetric; if this is < or > we need to flip if going to assume ordered: (arg op context).
        if(op.equals(ExprBinary.Op.GT)) return ExprBinary.Op.LT;
        else if(op.equals(ExprBinary.Op.LT)) return ExprBinary.Op.GT;
        else if(op.equals(ExprBinary.Op.GTE)) return ExprBinary.Op.LTE;
        else if(op.equals(ExprBinary.Op.LTE)) return ExprBinary.Op.GTE;
        else return op;               
    }

    public static Op negateBinaryOperator(Op op) {
        // DO NOT CONFUSE with flipBinaryOperator
        if(op.equals(ExprBinary.Op.GT)) return ExprBinary.Op.LTE;
        else if(op.equals(ExprBinary.Op.LT)) return ExprBinary.Op.GTE;
        else if(op.equals(ExprBinary.Op.GTE)) return ExprBinary.Op.LT;
        else if(op.equals(ExprBinary.Op.LTE)) return ExprBinary.Op.GT;
        else return op;               
    }
    
    /**
     * When building provenance for e1 op e2, 
     * if e2 is constant, then (e2 = c) needs to be added as an alpha.
     */
    private ProvenanceTree addFixedEquality(ProvenanceTree almost, Expr cause) throws Err {            
        int nValue = extractIntFromTupleSet(evaluate(orig, contextNumericOther));
        ProvenanceLeaf context = new ProvenanceLeaf(contextNumericOther.equal(ExprConstant.makeNUMBER(nValue)));
        List<ProvenanceTree> lst = new ArrayList<ProvenanceTree>(2);
        lst.add(context);
        lst.add(almost);
        return ProvenanceNode.construct(ProvenanceNode.Op.PAND, cause, currentSign, lst);
    }

    
    private ProvenanceTree buildNumericBinaryFormulaB(Expr cause, Expr left, Op op) throws Err {       
        int nValue = extractIntFromTupleSet(evaluate(orig, contextNumericOther));   
        //debug("buildNumericBinaryFormulaB for cause: "+cause+"; left="+left+"; op="+op+"; nValue="+nValue);
        if(op.equals(ExprBinary.Op.EQUALS)) {           
            return buildEqualProvenance(cause, left, nValue);
        } else {
            Expr desugared = desugarInequality(op, orig, currentSign, left, nValue, cause);            
            //debug("buildNumericBinaryFormulaB desugared: "+desugared);
            return desugared.accept(this);            
        }
    }

    static public Expr desugarInequality(Op op, A4Solution orig, boolean sign, Expr left, int nValue, Expr cause) throws Err {
        IntIterator it = orig.debugExtractKInstance().ints().iterator();
        List<Expr> subs = new ArrayList<Expr>();
        
        // If in negative currentSign (talking about success, rather than failure)
        // talk about the success of the negation of op.         
        if(!sign) {
            op = negateBinaryOperator(op);            
        }
        while(it.hasNext()) {
            int possibleValue = it.next();
            boolean usable;            
            if(op.equals(ExprBinary.Op.GT))  {                
                usable = possibleValue > nValue;                
            }
            else if(op.equals(ExprBinary.Op.LT)) {
                usable = possibleValue < nValue;
            }
            else if(op.equals(ExprBinary.Op.GTE)) {
                usable = possibleValue >= nValue;
            }
            else if(op.equals(ExprBinary.Op.LTE)) { 
                usable = possibleValue <= nValue;
            } else {
                throw new ErrorFatal("Amalgam found unsupported operator when building numeric binary formula: "+cause);
            }

            // this possibleValue satisfies the operator. generate disjunction that includes this equality
            if(usable) {
                Tuple itup = buildIntTuple(orig, possibleValue);
                Expr itupe = AmalgamVisitorHelper.tuple2Expr(orig, itup);
                subs.add(itupe.in(left));
            }
        }
        Expr desugared = ExprList.make(cause.pos, cause.closingBracket, ExprList.Op.OR, subs);
                
        return desugared;
    }

    private ProvenanceTree buildEqualProvenance(Expr cause, Expr left, int nValue) throws Err {
        Tuple oldContext = this.currentTupleIfAtomic;
        this.currentTupleIfAtomic = buildIntTuple(orig, nValue); // set context to nValue
        //System.err.println("buildEqualProvenance: descending for "+left);
        ProvenanceTree almostResult = left.accept(this);         // descend with this context
        this.currentTupleIfAtomic = oldContext;                  // restore any old context (shouldn't be any)
        return almostResult;
    }

    private void mustHaveTupleContext(Expr x) throws Err {
        if(currentTupleIfAtomic == null)
            throw new ErrorFatal("Relational expression had no tuple context: "+x);
    }

    @Override
    public ProvenanceTree visit(ExprList x) throws Err {
        debug("Visiting ExprList expression ", x);
        boolean diff = diffResultsHelperSanityCheck(x);        
        if(diff) {                                                            
            if(x.op == ExprList.Op.TOTALORDER)
                return AmalgamVisitorHelper.desugarTOTALORDER(x).accept(this);
            if(x.op == ExprList.Op.DISJOINT)
                return AmalgamVisitorHelper.desugarDISJOINT(x).accept(this);
            
            List<ProvenanceTree> subs = new ArrayList<ProvenanceTree>();

            if(isANDContext(x, currentSign)) { 
                // a1 /\ ... /\ an    --- any ai that fails causes the fmla to fail
                // So recur into fmlas that fail (ignore non-failing fmlas)
                for(Expr e : x.args) {                    
                    if(diffResultsHelper(e)) {
                        // If this subformula was an instantiation, pop that instantiation onto provBindings.
                        //  ...and annotate appropriately
                        Annotation a;
                        if(qBindings.containsKey(e)) {
                            this.provBindings.put(qBindings.get(e).a, qBindings.get(e).b);
                            a = new ProvenanceTree.PABindForall(qBindings.get(e).a, qBindings.get(e).b);
                        } else {
                            a = new ProvenanceTree.PAFollowAND();
                        }
                        
                        subs.add(e.accept(this).annotate(a));
                        if(qBindings.containsKey(e)) {
                            this.provBindings.remove(qBindings.get(e).a);
                        }
                    }
                }
                ProvenanceTree result = ProvenanceNode.construct(ProvenanceNode.Op.POR, x, currentSign, subs);
                //debug("  ~~~  AND context produced provenance tree: "+result);
                return result.annotate(new ProvenanceTree.PADesugarANDContext());                
            }

            else if(isORContext(x, currentSign)) {
                // a1 \/ ... \/ an \/ b1 \/ ... \/ bn -- if alphas change and betas remain the same, need *all* betas to fail (alphas must be false)
                for(Expr e : x.args) {
                    // recur into this formula (all of them must change sign)
                    Annotation aTry;
                    Annotation aUnavailable;
                    if(qBindings.containsKey(e)) {
                        aTry = new ProvenanceTree.PATryExist(qBindings.get(e).a, qBindings.get(e).b);
                        aUnavailable = new ProvenanceTree.PAUnavailableExist(qBindings.get(e).a, qBindings.get(e).b);
                    } else {
                        aTry = new ProvenanceTree.PATryOr();
                        aUnavailable = new ProvenanceTree.PAUnavailableOr();
                    }
                    if(diffResultsHelper(e)) subs.add(e.accept(this).annotate(aTry));
                    // remains either true or false; part of antecedent (so need to make implicit sign explicit)
                    else {
                        // going from true to false. Flip sign of antecedent because converting OR to IMPLIES
                        if(currentSign) subs.add(new ProvenanceLeaf(e.not()).annotate(aUnavailable)); 
                        // going from false to true. Flip sign + distribute negation inside = double negative
                        if(!currentSign) subs.add(new ProvenanceLeaf(e).annotate(aUnavailable));
                    }
                }
                ProvenanceTree result = ProvenanceNode.construct(ProvenanceNode.Op.PAND, x, currentSign, subs);
                //debug("  ~~~  OR context produced provenance tree: "+result);
                return result.annotate(new ProvenanceTree.PADesugarORContext());
            }
            else
                throw new ErrorFatal("Unsupported nary op: "+x);
        } else {     
            throw new ErrorFatal("Called Amalgam diff eval on ExprList that didn't change value: "+x);
        }
    }

    @Override
    public ProvenanceTree visit(ExprCall x) throws Err {
        debug("Visiting ExprCall expression ", x);
        boolean diff = diffResultsHelperSanityCheck(x);
        if(diff) {
            // Record this call site in the provenance tree, otherwise highlighting
            // jumps around the spec confusingly.
            
            ProvenanceTree resolved = AmalgamVisitorHelper.resolveExprCall(x).accept(this).disallowCollapse();            
            return ProvenanceNode.construct(ProvenanceNode.Op.PAND, x, this.currentSign, Collections.singletonList(resolved))
                    .disallowCollapse().annotate(new ProvenanceTree.PAResolveCall());
        }
        throw new ErrorFatal("Called Amalgam diff eval on ExprCall that didn't change value: "+x);

    }

    @Override
    public ProvenanceTree visit(ExprConstant x) throws Err {
        debug("Visiting ExprConstant expression ", x);
        if(!diffResultsHelperSanityCheck(x)) {
            throw new ErrorFatal("Called Amalgam diff eval on ExprConstant that didn't change value: "+x);
        }

        // Some constant expressions can differ. IDEN, for instance, will be restricted to atoms used in the model.
        // "Used in the model" is defined as the union of all top-level sigs.
        if(ExprConstant.Op.IDEN.equals(x.op)) {                        
            // Whether or not a concrete tuple has the same first and second atom CANNOT change.
            // However, this portion can:
            Expr desugared = Sig.UNIV.product(Sig.UNIV);
            return desugared.accept(this).annotate(new ProvenanceTree.PAExpandIDEN());            
        }         
        
        // Even if can't differ, might be an antecedent in an explanation.        
        diffCache.put(x, false);
        Expr ground = tuple2Expr(orig, currentTupleIfAtomic).in(x);
        return new ProvenanceLeaf(ground); // TODO sign?                 
    }

    @Override
    public ProvenanceTree visit(ExprITE x) throws Err {
        // if C do X else Y

        debug("Visiting ExprITE expression ", x);

        boolean diff = diffResultsHelperSanityCheck(x);
        if(diff) {
            Expr desugared = x.cond.and(x.left).or(x.cond.not().and(x.right));                        
            return desugared.accept(this).annotate(new ProvenanceTree.PADesugarITE());
        }


        throw new ErrorFatal("ExprITE in diff-eval but expression value did not differ between models.");
    }

    @Override
    public ProvenanceTree visit(ExprLet x) throws Err {
        debug("Visiting ExprLet expression; desugaring ", x);

        // Substitute the let variable in the subexpression
        Expr desugared = x.sub.accept(new AmalgamSubstituteVisitor(x.var, x.expr, false));
        return desugared.accept(this).annotate(new ProvenanceTree.PADesugarLet());                
    }

    @Override
    public ProvenanceTree visit(ExprQt x) throws Err {
        debug("Visiting ExprQt expression; decls size="+x.decls.size()+" ", x);
        if(x.decls.size() > 0) {
            debug("    First decl had expr ", x.decls.get(0).expr);
        }

        boolean diff = diffResultsHelperSanityCheck(x); 
        if(diff) {   
            if(x.op.equals(ExprQt.Op.COMPREHENSION)) {
                debug("desugarComprehension: ", x);
                return AmalgamVisitorHelper.desugarComprehension(orig, x, currentTupleIfAtomic).accept(this).annotate(new ProvenanceTree.PADesugarComprehension());
            } else if(x.op.equals(ExprQt.Op.SUM)) {
                return visitSum(x); // no annotation; unsupported
            } else {                
                Expr desugared = desugarQuantifier(x); 
                debug("    Desugared quantifier to ", desugared);     
                if(!diffResultsHelperSanityCheck(desugared)) {
                    throw new ErrorFatal("Differing-value quantifier desugared but result didn't change value:\n"+x+"\n"+desugared);
                }
                if(desugared instanceof ExprQt)
                    return visitQuantifier((ExprQt)desugared);
                else // 2nd branch occurs if we've desugared "one" 
                    return desugared.accept(this); // no annotation
            }              
        } else {
            throw new ErrorFatal("Called Amalgam diff evaluator on expression that did not differ: "+x);
        }
    }

    private ProvenanceTree visitSum(ExprQt x) throws Err {
        throw new ErrorFatal("sum numeric operator not yet supported by Amalgam"); 
    }    

    private ProvenanceTree visitQuantifier(ExprQt x) throws Err {
        // Quantified: have *many* potential subexpressions w/ quantified var instantiated

        // Alloy's eval function just translates to Kodkod and then uses Kodkod's eval function
        // We need to instantiate *Alloy* expressions. 
        // Take advantage of the fact that Alloy creates a sig for each atom; build each into an expr and substitute.

        if(!diffResultsHelperSanityCheck(x)) {
            throw new ErrorFatal("Called visitQuantifier on expression that did not differ: "+x);
        }
        
        ///////////////////
        // all/some v: T | F(x) 
        ///////////////////

        // Get v and T
        ExprHasName v = getQtSingleVar(x);
        Expr T = getQtSingleVarExpr(x);                
        // Get set of potential instantiations
        TupleSet upperBoundInstantiations = T.accept(new AmalgamUpperBoundVisitor(root, orig));        

        //debug("visitQuantifier: "+x+" got v="+v+"; T="+T+"\n      UB instantiations (raw tuples) ="+upperBoundInstantiations);
        //debug("visitQuantifier with orig.atom2name="+orig.atom2name+" and getAllAtoms()="+orig.getAllAtoms());
        
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
            //debug("visitQuantifier SUBSTITUTED: "+v+" ~> "+instantiation+" (was tuple: "+tup+"). Produced "+substituted);            

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

            qBindings.put(qinst, new Pair<ExprHasName, Object>(v, tup)); // remember this binding was taken
            subExprs.add(qinst);
        }

        Expr desugared = ExprList.make(x.pos, x.closingBracket, (x.op.equals(ExprQt.Op.ALL) ? ExprList.Op.AND : ExprList.Op.OR), subExprs);        
        return desugared.accept(this).annotate(new ProvenanceTree.PADesugarQuantifier(v));        
    }

    private ExprUnary lastNOOP = null; 
    
    @Override
    public ProvenanceTree visit(ExprUnary x) throws Err {
        debug("Visiting ExprUnary (op="+x.op+") expression ", x);                     
        boolean diff = diffResultsHelperSanityCheck(x);        
        if(diff) {
            // ignore no-ops
            // Except that sometimes NOOP has the real source location of a Field's use and the Field has the declaration site
            // Remember the most recent NOOP so we can use the proper location if needed.
            if(x.op.equals(ExprUnary.Op.NOOP)) {                
                lastNOOP = x;
                ProvenanceTree result = x.sub.accept(this);
                return result;
            }

            // *********************************
            // Limited integer operator support
            // *********************************
            
            // casts are effectively no-ops for integers
            else if(x.op.equals(ExprUnary.Op.CAST2INT) ||
                    x.op.equals(ExprUnary.Op.CAST2SIGINT)) {
                return x.sub.accept(this);
            }

            else if(x.op.equals(ExprUnary.Op.CARDINALITY)) {
                if(contextNumericOther == null)                
                    throw new ErrorFatal("Cardinality unary operator visited without context: "+x);

                if(!currentSign) {
                    // not #e = contextNumericOther. desugar as disjunction of all possibilities != context.
                    // Note that where the positive case (else) uses x.sub directly, we use x here to retain the #
                    IntIterator it = orig.debugExtractKInstance().ints().iterator();
                    List<Expr> neqpossibilities = new LinkedList<Expr>();
                    int currval = extractIntFromTupleSet(evaluate(orig, contextNumericOther));
                    while(it.hasNext()) {
                        int v = it.next();                        
                        if(v != currval && v >= 0) {
                            neqpossibilities.add(x.equal(ExprConstant.makeNUMBER(v))); // #e = <other val>
                        }
                    }
                    Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, neqpossibilities);
                    currentSign = true;
                    // Now asking about *failure* of OR of other options
                    ProvenanceTree result = desugared.accept(this).annotate(new ProvenanceTree.PADesugarUnary(x.op));
                    currentSign = false;
                    return result;
                } else {
                    // #e = contextNumericOther. desugar as <conjunction of unchanging> implies <disjunction of changing>
                    // for reasoning about this model, 
                    // it suffices to know how the <current combo> of tuples fails to satisfy the cardinality expected.
                    // To desugar non-locally, we'd do <unchanged n> => <disjunction of all combinations of <changed goal-n>
                    // but all but one consequent will be _false_ in original model; only one fails when L is flipped.

                    //Object answer = orig.eval(contextNumericOther);
                    //int bucketSize = extractIntFromTupleSet(answer);

                    List<Expr> localChanged = new ArrayList<Expr>();
                    List<Expr> localUnchanged = new ArrayList<Expr>();

                    TupleSet ub = x.sub.accept(new AmalgamUpperBoundVisitor(root, orig));

                    A4TupleSet xsubOrig = (A4TupleSet)    evaluate(orig, x.sub);
                    A4TupleSet xsubFlipped = (A4TupleSet) evaluate(flipped, x.sub);
                    for(Tuple t : ub) {                    
                        Expr texpr = AmalgamVisitorHelper.tuple2Expr(orig, t);
                        boolean inOrig = xsubOrig.debugGetKodkodTupleset().contains(t);
                        boolean inFlipped = xsubFlipped.debugGetKodkodTupleset().contains(t);

                        if(inOrig && inFlipped) {          // stays true              
                            localUnchanged.add(texpr.in(x.sub));
                        } else if(!inOrig && !inFlipped) { // stays false
                            localUnchanged.add(texpr.in(x.sub).not());
                        } else if(!inOrig && inFlipped) {  // was false
                            localChanged.add(texpr.in(x.sub).not());
                        } else {                           // was true
                            localChanged.add(texpr.in(x.sub));
                        }
                    }

                    //debug("Amalgam: cardinality constraint for "+x.sub+" produced: "+local);
                    Expr desugaredUnchanged = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, localUnchanged); 
                    Expr desugaredChanged = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, localChanged);
                    Expr desugared = desugaredUnchanged.implies(desugaredChanged); 
                    return desugared.accept(this).annotate(new ProvenanceTree.PADesugarUnary(x.op)); 
                }
            }

            
            // *********************************
            // Boolean unary operators
            // *********************************

            // Flip sign of context if needed
            else if(x.op.equals(ExprUnary.Op.NOT)) {
                currentSign = !currentSign;
                ProvenanceTree result = x.sub.accept(this).annotate(new ProvenanceTree.PADesugarUnary(x.op));
                currentSign = !currentSign;
                return result;
            } 
            else if(x.op.equals(ExprUnary.Op.SOME)) {
                // Cannot desugar this as a single quantifier. Need the entire tuple. 
                // (Note this is less efficient than a some for *solving* but for evaluation should be similar.)  
                // Also cannot make this a sequence of quantifiers over univ; univ definition is union of top level sorts.
                // which for a why-not? may lead to pre-desugar differing but post-desugar NOT differing.

                TupleSet upperBoundInstantiations = x.sub.accept(new AmalgamUpperBoundVisitor(root, orig));
                if(upperBoundInstantiations.size() < 1) 
                    throw new ErrorFatal("DiffEval on some E but E had empty upper bound: "+x.sub);

                List<Expr> subFmlas = new ArrayList<Expr>(); 
                for(Tuple instantiation : upperBoundInstantiations) {
                    Expr tup = tuple2Expr(orig, instantiation);
                    subFmlas.add(tup.in(x.sub));
                }

                Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, subFmlas);                                               
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarUnary(x.op));
            }
            else if(x.op.equals(ExprUnary.Op.LONE)) {
                // desugar as one or no
                return x.sub.one().or(x.sub.no()).accept(this).annotate(new ProvenanceTree.PADesugarUnary(x.op));
            }
            else if(x.op.equals(ExprUnary.Op.ONE)) {
                // Similar to SOME case, except with further nesting to ensure uniqueness.
                TupleSet upperBoundInstantiations = x.sub.accept(new AmalgamUpperBoundVisitor(root, orig));
                if(upperBoundInstantiations.size() < 1) 
                    throw new ErrorFatal("DiffEval on some E but E had empty upper bound");

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
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarUnary(x.op));                              
            }            
            else if(x.op.equals(ExprUnary.Op.NO)) {
                // desugar as not some
                Expr desugared = x.sub.some().not();
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarUnary(x.op));
            }

            // *********************************
            // Relational unary operators
            // *********************************

            // SETOF is vaguely like a no-op in this context. inserted by type decl fmla building
            // Note that this assumes a tuple context is present! So we are evaluating something like
            // Node$1->Node$2 in set this/Node. Treating this as a NOOP in a quantifier Decl would be unsafe. 
            else if(x.op.equals(ExprUnary.Op.SETOF)) {                
                return x.sub.accept(this); // no annotation
            }

            else if(x.op.equals(ExprUnary.Op.CLOSURE)) {
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
                ProvenanceTree result = desugared.accept(this).annotate(new ProvenanceTree.PADesugarUnary(x.op));
                currentTupleIfAtomic = saveTuple;
                return result;
            }
            else if(x.op.equals(ExprUnary.Op.RCLOSURE)) {
                mustHaveTupleContext(x);
                // sugar: remember to restrict IDEN
                Expr restrictedIden = ExprConstant.IDEN.intersect(Sig.UNIV.product(Sig.UNIV));
                Expr desugared = restrictedIden.plus(x.sub.closure());
                return desugared.accept(this).annotate(new ProvenanceTree.PADesugarUnary(x.op)); 
                // same context tuple
            }
            else if(x.op.equals(ExprUnary.Op.TRANSPOSE)) {
                mustHaveTupleContext(x);
                // flip the context tuple
                Tuple saveTuple = currentTupleIfAtomic;
                currentTupleIfAtomic = transposeTuple(orig, currentTupleIfAtomic);
                ProvenanceTree result = x.sub.accept(this);
                currentTupleIfAtomic = saveTuple;
                return result.annotate(new ProvenanceTree.PADesugarUnary(x.op));
            }
            else
                throw new ErrorFatal("Unsupported unary operator: "+x.op+" in "+x);            
        } else {
            throw new ErrorFatal("AmalgamEvalVisitor (unary) called on expression that didn't differ in value: "+x+
                    " with tuple context: "+currentTupleIfAtomic+"; value was: "+evaluate(orig, x)+" vs. "+evaluate(flipped, x)+". Flip Rel: "+flipRel+" Flip Tup: "+flipTup);
        }
    }

    public static int extractIntFromTupleSet(Object answer) throws ErrorFatal {
        // Evaluation will return an A4TupleSet containing a singleton integer
        //   Except that in the #e case it returns an integer. Note though that add[#e, 0] returns the singleton set, 
        //   and that #e in add[#e, 0] is true, so Alloy does implicit recasting.
        if(answer instanceof A4TupleSet) {
            A4TupleSet ts = (A4TupleSet)answer;
            Iterator<Tuple> it = ts.debugGetKodkodTupleset().iterator();
            if(!it.hasNext()) 
                throw new ErrorFatal("Evaluation result expected singleton set containing integer; got: "+answer+". Please make sure Alloy has a bitwidth>0 set.");
            Tuple t = it.next();
            Object atom = t.atom(0);
            if(atom instanceof Integer) return (Integer)atom;
            if(atom instanceof String) return Integer.parseInt((String)atom);
            throw new ErrorFatal("Evaluation result expected singleton set containing integer; got: "+answer+". Please make sure Alloy has a bitwidth>0 set.");
        } else if(answer instanceof Integer) {
            return (Integer)answer;
        } else {
            throw new ErrorFatal("Evaluation result expected integer or singleton set containing integer; got: "+answer);   
        }
    }

    public static Tuple buildIntTuple(A4Solution soln, int i) throws Err {
        // If only constants appear in the spec, Alloy may detect ints aren't needed and compile them out, 
        // resulting in bitwidth = 0 and eval(5) --> {} rather than {5}. This will cause Amalgam to fail: 
        // even if we detect an ExprConstant here, there would be no **VALID TUPLE** to map it to.
                
        TupleSet tups = soln.debugExtractKInstance().tuples(i);
        Iterator<Tuple> it = tups.iterator();
        if(!it.hasNext()) throw new ErrorFatal("buildIntTuple: no tuples in resulting set for "+i);
        return it.next();
    }
    
    @Override
    public ProvenanceTree visit(ExprVar x) throws Err {
        debug("Visiting ExprVar expression ", x);
        // If quantified variable, will be substituted out. If a let, should be resolved out. 
        // Otherwise it's something understandable at top level.
        //boolean diff = diffResultsHelperDebug(x);   
        //if(diff) {
        //    differingSubExpressions.add(x);
        //}

        // This must *fail*, and in tuple context.
        Expr ground = tuple2Expr(orig, currentTupleIfAtomic).in(x);
        return new ProvenanceLeaf(ground);
    }

    @Override
    public ProvenanceTree visit(Sig x) throws Err {
        if(!diffResultsHelperSanityCheck(x)) {
            throw new ErrorFatal("Called Amalgam diff eval on Sig that didn't change value: "+x);
        }
        if(currentTupleIfAtomic == null)
            throw new ErrorFatal("Had no tuple context when diff evaluating "+x);

        debug("Visiting Sig expression ", x);
        //debug("    flipTup="+flipTup+"; flipRel="+flipRel);
        //debug("    flipTup==context="+flipTup.equals(currentTupleIfAtomic)+"; flipRel==context="+flipRel.equals(x));
        // This must *fail*, and in tuple context.
        // XXX Here's the problem: flipRel.equals(x) 
        // there are model-level consequences if this Sig is defined via remainder
        // If B < A, we flip t in B. Then both A and B need the checking. 
        
        // UNIV is defined. Don't stop here.
        if(Sig.UNIV.equals(x)) {
            Expr desugared = null;
            for(Sig s : root.getAllReachableSigs()) {
                if(s.isTopLevel() && !Sig.UNIV.equals(s)) { // exclude UNIV or get infinite recursion
                    if(desugared == null) desugared = s;
                    else                  desugared = desugared.plus(s);
                }
            } // !!!
            if(desugared == null) {
                throw new ErrorFatal("Amalgam tried to desugar UNIV but had no top level sigs.");
            }            
            return desugared.accept(this).annotate(new ProvenanceTree.PAExpandUNIV());
        }
        
        
        if(flipTup.equals(currentTupleIfAtomic) && flippedRelOrSupertype(x)) {
            Expr tupleExpr = tuple2Expr(orig, currentTupleIfAtomic); 
            return new ProvenanceContradiction(x, tupleExpr, lastNOOP, this.provBindings);
        }
        Expr ground = tuple2Expr(orig, currentTupleIfAtomic).in(x);
        return new ProvenanceLeaf(ground);
    }

    @Override
    public ProvenanceTree visit(Field x) throws Err {
        if(!diffResultsHelperSanityCheck(x)) {
            throw new ErrorFatal("Called Amalgam diff eval on Field that didn't change value: "+x);
        }
        if(currentTupleIfAtomic == null)
            throw new ErrorFatal("Had no tuple context when diff evaluating "+x);

        debug("Visiting Field expression ", x);
        // This must *fail*, and in tuple context. No supertype concerns since no "superfields".
        if(flipTup.equals(currentTupleIfAtomic) && flipRel.equals(x)) {
            Expr tupleExpr = tuple2Expr(orig, currentTupleIfAtomic); 
            return new ProvenanceContradiction(x, tupleExpr, lastNOOP, this.provBindings);
        }
        Expr ground = tuple2Expr(orig, currentTupleIfAtomic).in(x);        
        return new ProvenanceLeaf(ground);
    }

    /** Is this sig the flipped relation, or a supertype of the flipped relation? */
    private boolean flippedRelOrSupertype(Sig x) {
        // XXX instanceof :(
        if(flipRel instanceof PrimSig) {
            PrimSig psf = (PrimSig)flipRel;
            // equal or some supertype of flipped is equal
            return psf.isSameOrDescendentOf(x);                        
        } else {
            return flipRel.equals(x);
        }
    }

    public Set<Expr> getDifferentExprsVisited() {
        Set<Expr> result = new HashSet<Expr>();
        for(Expr e : diffCache.keySet()) {
            if(diffCache.get(e)) {
                if(e instanceof ExprUnary && ((ExprUnary)e).op==ExprUnary.Op.NOOP){
                    // don't report NO-OP differences
                } else {
                    result.add(e);
                }
            }
        }
        return result;
    }
    
    // FOR DEBUGGING MEMORY USAGE
    /*protected void finalize() {
        System.out.println("Finalizing AmalgamEvalVisitor: "+this);
    }*/

    
}
