package edu.mit.csail.sdg.alloy4compiler.translator;

import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.buildSimplePaths;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.desugarQuantifier;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.getQtSingleVar;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.getQtSingleVarExpr;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.isANDContext;
import static edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper.isORContext;
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
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;

/**
 * Given an arbitrary expression, an arbitrary model...
 * ... constructs a provenance tree of facts in the models that entail the expression
 */
public class AmalgamGroundVisitor extends VisitReturn<ProvenanceTree> {
    private static final boolean nobranch = true;         
    final A4Solution origModelForTupleGeneration;
    final A4Solution model;
    final Module root;    
    private boolean currentSign = true;
    private Tuple currentTupleIfAtomic = null;
    private long sanityCheckCount = 0;
    
    /** Pass in the overall expression being explained so that exceptions can communicate the high-level cause as well. */
    private Expr explainingExprForError;

    public AmalgamGroundVisitor(Module root, A4Solution origModelForTupleGeneration, A4Solution model, Expr explainingExprForError) throws Err {
        this.origModelForTupleGeneration = origModelForTupleGeneration;
        this.model = model; 
        this.root = root;
        this.explainingExprForError = explainingExprForError;
        
        /* XXX We ought to only need one model here. And yet, if we try to use <model> for tuple2Expr, 
         *     some relations seem to be missing. In the interest of time, leaving this old 2-model architecture.
         */
        
        if(AmalgamVisitorHelper.sanityCheck) {
            if(!model.debugExtractKInstance().relations().equals(origModelForTupleGeneration.debugExtractKInstance().relations())) {
                System.err.println("Instantiating Ground Visitor.\nOrig="+origModelForTupleGeneration.debugExtractKInstance().relations()+"\nmodel="+model.debugExtractKInstance().relations());
                throw new ErrorFatal("AmalgamGroundVisitor: non-equal relation sets");            
            }
        }
        // TODO assume only called within single EvalVisitor 
        //AmalgamVisitorHelper.clearExprCache();                
    }

    public void debug(String msg, Expr x) throws Err {
        if(AmalgamVisitorHelper.debugGround) {
            System.err.println("########## Amalgam GROUND Visitor Debug (currentSign="+currentSign+" currTup="+currentTupleIfAtomic+
                    "; eval="+model.eval(x)+"; count="+sanityCheckCount+"): "+msg);
        }
    }

    // Fail early if the visitor goes haywire
    public void protectAndError(Expr x) throws Err {
        sanityCheckCount++;
        if(!AmalgamVisitorHelper.sanityCheck) return;
        
        Object res = model.eval(x);
        if(res instanceof Boolean) {
            Boolean resb = (Boolean) res;
            if(resb != currentSign) 
                throw new ErrorFatal("AmalgamGroundVisitor visited a formula that evaluated to the wrong sign. Expected "+
                                     currentSign+" but got "+resb+".\ncurrSign="+currentSign+"; currTuple="+currentTupleIfAtomic+"\n"+
                                     "Fmla was "+x+"\nmodel was=\n"+model.debugExtractKInstance()+"\n"+
                                     "Alpha context being explained: "+this.explainingExprForError);
        } else if (res instanceof A4TupleSet) {
            //A4TupleSet resset = (A4TupleSet) res;
            if(currentTupleIfAtomic == null) 
                throw new ErrorFatal("AmalgamGroundVisitor visited an expression within a null tuple context: "+x);

            // TODO: is the tuple in the set? (should depend on currentsign)

        } else if (res instanceof Integer) {
            // do nothing; it's fine
        } else
            throw new ErrorFatal("AmalgamGroundVisitor: Evaluation produced non-tupleset, non-boolean, non-Integer: "+x+" -->"+res+" : "+res.getClass().getName());
    }
    
    @Override
    public ProvenanceTree visit(ExprBinary x) throws Err {
        protectAndError(x);
        debug("Visiting ExprBinary expression: "+x, x);
        
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
            return desugared.accept(this);
        }
        else if(x.op.equals(ExprBinary.Op.IFF)) {
            // sugar
            Expr case1 = ExprBinary.Op.AND.make(x.pos, x.closingBracket, x.left, x.right);
            Expr case2 = ExprBinary.Op.AND.make(x.pos, x.closingBracket, x.left.not(), x.right.not());                
            Expr desugared = ExprBinary.Op.OR.make(x.pos, x.closingBracket, case1, case2);
            return desugared.accept(this);
        }
        else if(x.op.equals(ExprBinary.Op.IMPLIES)) {
            // sugar
            Expr desugared = ExprBinary.Op.OR.make(x.pos, x.closingBracket, x.left.not(), x.right);
            return desugared.accept(this);
        }
        // ***************************************
        // R1 in R2: desugaring case
        // tup in R: base Boolean case
        // ***************************************
        else if(x.op.equals(ExprBinary.Op.IN)) {
            // The two instances share bounds, so it doesn't matter which is passed in here. 
            TupleSet ub = x.left.accept(new AmalgamUpperBoundVisitor(root, model));
            debug("isINContext: "+x+" ~~ ub(left)="+ub+" isGroundLHS="+AmalgamVisitorHelper.isGroundProduct(x.left), x);
            // True base case: tuple in EXPR, can't desugar LHS any more
            if(AmalgamVisitorHelper.isGroundProduct(x.left) && ub.size() == 1) { 
                debug("isINContext: true base case: "+x, x);
                currentTupleIfAtomic = ub.iterator().next();
                ProvenanceTree result = x.right.accept(this);
                currentTupleIfAtomic = null;
                return result;
            } 
            // General EL in ER
            else if(ub.size() > 0) {
                // Desugar LHS                
                debug("Complex IN formula; calling isIn on: ", x);
                // If we have something like "R in one X"; desugar to get rid of multiplicity.
                Expr xmult = AmalgamVisitorHelper.isIn(x.left, x.right,true);
                if(xmult != null) {
                    return xmult.accept(this);
                } else {
                    debug("isINContext: desugaring: "+x, x);
                    List<ProvenanceTree> cases = new ArrayList<ProvenanceTree>();                 
                    for(Tuple tup : ub) {
                        // for each t, ~(t in left) \/ t in right must hold.
                        Expr tupExpr = tuple2Expr(origModelForTupleGeneration, tup);
                        // justify each LHS tuple...
                        Expr groundL = tupExpr.in(x.left);
                        Expr groundR = tupExpr.in(x.right);
                        boolean resL = (Boolean)model.eval(tupExpr.in(x.left)); 
                        boolean resR = (Boolean)model.eval(tupExpr.in(x.right));  
                        debug("     justifcation of x.left, x.right for t="+tup+": left="+resL+" right="+resR, x);
                        // L IN R
                        if(currentSign) {
                            // 1. In LHS and RHS
                            if(resL && resR) {                        
                                // recur on t in LHS /\ t in RHS
                                Expr desugared = ExprBinary.Op.AND.make(x.pos, x.closingBracket, groundL, groundR);
                                debug("     desugared to: "+desugared, x);
                                cases.add(desugared.accept(this));                                                
                            } 
                            // 2. Not in LHS
                            else if (!resL) {
                                Expr desugared = groundL.not(); 
                                debug("     desugared to: "+desugared, x);
                                cases.add(desugared.accept(this));      
                            }
                            // This should throw an error since success is universal (has to apply to all tuples)
                            else if (resL && !resR) throw new ErrorFatal("Tried justifying a set containment with a missing tuple: "+x);
                            if(!cases.isEmpty() && nobranch) break;
                        }
                        // L NOT IN R
                        else {
                            // 1. In LHS and not in RHS
                            if(resL && !resR) {                        
                                // recur on t in LHS /\ t not in RHS
                                Expr desugared = ExprBinary.Op.AND.make(x.pos, x.closingBracket, groundL, groundR.not()).not();
                                debug("     desugared to: "+desugared, x);                            
                                cases.add(desugared.accept(this));                                                
                            } 
                            // This is fine; this *particular* tuple just isn't a failure witness!
                            //else if (resL && resR) throw new ErrorFatal("Tried justifying a set exclusion with an extra tuple: "+x);
                        }
                    }
                    // *any* tuple failure suffices to justify failure
                    // *all* tuples must succeed to justify success
                    ProvenanceTree result;
                    if(currentSign)
                        result = ProvenanceNode.construct(ProvenanceNode.Op.POR, x, currentSign, cases);
                    else
                        result = ProvenanceNode.construct(ProvenanceNode.Op.PAND, x, currentSign, cases);
                    debug("  ~~~  IN context ("+x+") produced provenance tree: "+result+"; cases.size()="+cases.size(), x);
                    return result;
                } 
            } else {
                // Here, if upper-bound is empty, it is because of the bounds.
                if(currentSign) return new ProvenanceConstantLeaf(ProvenanceConstantLeaf.TYPE.TRUE_WRT_BOUNDS, x);
                else return new ProvenanceConstantLeaf(ProvenanceConstantLeaf.TYPE.FALSE_WRT_BOUNDS, x);
                //throw new ErrorFatal("Encountered an empty LHS upper-bound tuple set when processing: "+x);
            }
        }
        else if(x.op.equals(ExprBinary.Op.NOT_IN)) {
            currentSign = !currentSign;
            Expr desugared = x.left.in(x.right);
            return desugared.accept(this);
        }
        else if(x.op.equals(ExprBinary.Op.EQUALS)) {
            if(AmalgamVisitorHelper.isNumericExpr(x.left) || AmalgamVisitorHelper.isNumericExpr(x.right))
            {        
                // If trying to see why e1 = e2 is *false*, suffices to see why e1 = eval(e1) and e2 = eval(e2).
                //    Hence this descent always swaps to positive even if the equality fails.               
                boolean oldSign = this.currentSign;
                this.currentSign = true;
                // We need to know why, in this model, {val1} in x.left and {val2} in x.right
                int nValueLeft = AmalgamEvalVisitor.extractIntFromTupleSet(model.eval(x.left)); 
                int nValueRight = AmalgamEvalVisitor.extractIntFromTupleSet(model.eval(x.right));
                Tuple oldTuple = this.currentTupleIfAtomic;
                this.currentTupleIfAtomic = AmalgamEvalVisitor.buildIntTuple(model, nValueLeft); 
                ProvenanceTree leftResult = x.left.accept(this);
                this.currentTupleIfAtomic = AmalgamEvalVisitor.buildIntTuple(model, nValueRight);
                ProvenanceTree rightResult = x.right.accept(this);
                this.currentTupleIfAtomic = oldTuple;
                this.currentSign = oldSign;
                
                List<ProvenanceTree> lst = new ArrayList<ProvenanceTree>(2);
                lst.add(leftResult); lst.add(rightResult);                
                return ProvenanceNode.construct(ProvenanceNode.Op.PAND, x, currentSign, lst);
            } else {                        
                // desugar as 2 ins:
                Expr desugared = x.left.in(x.right).and(x.right.in(x.left));
                return desugared.accept(this);
            }
        }
        else if(x.op.equals(ExprBinary.Op.NOT_EQUALS)) {
            // desugar
            Expr desugared = x.left.equal(x.right).not();
            return desugared.accept(this);                
        }        
        // ***************************************
        // Relational binary expressions
        // ***************************************
        else if(x.op.equals(ExprBinary.Op.PLUS)) {
            mustHaveTupleContext(x);
            // desugar as \/       
            Tuple saveTuple = currentTupleIfAtomic;
            Expr desugared1 = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x.left); 
            Expr desugared2 = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x.right);
            currentTupleIfAtomic = null; // back in Boolean context
            ProvenanceTree result = desugared1.or(desugared2).accept(this); 
            currentTupleIfAtomic = saveTuple; // return to Relational context
            return result;
        }
        else if(x.op.equals(ExprBinary.Op.INTERSECT)) {
            mustHaveTupleContext(x);
            // desugar as /\       
            Tuple saveTuple = currentTupleIfAtomic;
            Expr desugared1 = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x.left); 
            Expr desugared2 = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x.right);
            currentTupleIfAtomic = null; // back in Boolean context
            ProvenanceTree result = desugared1.and(desugared2).accept(this); 
            currentTupleIfAtomic = saveTuple; // return to Relational context
            return result;
        }
        else if(x.op.equals(ExprBinary.Op.DOMAIN)) {
            mustHaveTupleContext(x);
            // t in A <: B  means t in B and the first component of t is in A.  
            Expr inRight = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x.right);
            Expr inLeftFirst = tuple2Expr(origModelForTupleGeneration, projectTuple(model, currentTupleIfAtomic, 0)).in(x.left);
            List<Expr> lst = new ArrayList<Expr>(2);
            lst.add(inRight);
            lst.add(inLeftFirst);
            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, lst);
            return desugared.accept(this);
        }
        else if(x.op.equals(ExprBinary.Op.RANGE)) {
            mustHaveTupleContext(x);
            // t in B :> A  means t in B and the last component of t is in A.  
            Expr inLeft = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x.left);
            Expr inRightLast = tuple2Expr(origModelForTupleGeneration, projectTuple(model, currentTupleIfAtomic, currentTupleIfAtomic.arity()-1)).in(x.right);
            List<Expr> lst = new ArrayList<Expr>(2);
            lst.add(inRightLast);
            lst.add(inLeft);
            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, lst);
            return desugared.accept(this);
        }
        else if(x.op.equals(ExprBinary.Op.JOIN)) {
            mustHaveTupleContext(x);

            // Desugar as large disjunction. 
            // t in A.B (A nary, B mary) ~~> \/ [ta, tb in UBs | ta.tb = t] (ta in A /\ tb in B)                                

            TupleSet ubLeft = x.left.accept(new AmalgamUpperBoundVisitor(root, model));
            TupleSet ubRight = x.right.accept(new AmalgamUpperBoundVisitor(root, model));

            List<Expr> possibilities = new ArrayList<Expr>();
            for(Tuple ta : ubLeft) {
                for(Tuple tb : ubRight) {
                    // Does this pair join into t?
                    Tuple tj = joinTuple(origModelForTupleGeneration, ta, tb);
                    if(currentTupleIfAtomic.equals(tj)) // joinTuple returns null if they don't join
                    {
                        Expr exprTA = tuple2Expr(origModelForTupleGeneration, ta);
                        Expr exprTB = tuple2Expr(origModelForTupleGeneration, tb);
                        Expr possibility = exprTA.in(x.left).and(exprTB.in(x.right));
                        possibilities.add(possibility);
                    }
                }                    
            }
            if(possibilities.isEmpty()) {
                //throw new ErrorFatal("Empty JOIN desugar: "+currentTupleIfAtomic+" not in "+x);
                if(currentSign) return new ProvenanceConstantLeaf(ProvenanceConstantLeaf.TYPE.TRUE_WRT_BOUNDS, x);
                else return new ProvenanceConstantLeaf(ProvenanceConstantLeaf.TYPE.FALSE_WRT_BOUNDS, x);
            }
            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, possibilities);
            Tuple saveTuple = currentTupleIfAtomic;
            currentTupleIfAtomic = null;
            ProvenanceTree result = desugared.accept(this);
            currentTupleIfAtomic = saveTuple;
            return result;
        }
        else if(x.op.equals(ExprBinary.Op.MINUS)) {
            mustHaveTupleContext(x);
            // desugar as /\ (with negation on RHS)
            Tuple saveTuple = currentTupleIfAtomic;
            Expr desugared1 = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x.left); 
            Expr desugared2 = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x.right).not();
            currentTupleIfAtomic = null; // back in Boolean context
            ProvenanceTree result = desugared1.and(desugared2).accept(this); 
            currentTupleIfAtomic = saveTuple; // return to Relational context
            return result;            
        }
        else if(x.op.equals(ExprBinary.Op.PLUSPLUS)) {
            mustHaveTupleContext(x);
            // Relational override with tuple context on LHS: desugar as OR of 2 cases:
            Expr inRight = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x.right);
            Expr inLeft = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x.left);

            Expr firstColumnTuple = tuple2Expr(origModelForTupleGeneration, projectTuple(origModelForTupleGeneration, currentTupleIfAtomic, 0));
            Expr firstColumnRight = x.right;
            while(firstColumnRight.type().arity() > 1) {
                // keep joining univ onto right until we have a unary relation: the leftmost column
                firstColumnRight = firstColumnRight.join(Sig.UNIV);
            }
            Expr firstInRight = firstColumnTuple.in(firstColumnRight);
            Expr inLeftFirstNotInRight = inLeft.and(firstInRight.not()); 
            
            List<Expr> lst = new ArrayList<Expr>(2);
            
            lst.add(inRight);
            lst.add(inLeftFirstNotInRight);
            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, lst);
            return desugared.accept(this);
        }
        else if(x.op.equals(ExprBinary.Op.ARROW)) {
            // XXX TN copied this directly from new code in EvalVisitor. 
            mustHaveTupleContext(x);
            // RHS: A->B with tuple context for LHS: desugar as AND of 2 subtuple membership exprs.

            Tuple leftTupleContext = projectTupleRange(origModelForTupleGeneration, currentTupleIfAtomic, 0, x.left.type().arity());
            Tuple rightTupleContext = projectTupleRange(origModelForTupleGeneration, currentTupleIfAtomic, x.left.type().arity(), x.right.type().arity()); 
            List<Expr> fmlas = new ArrayList<Expr>(2);
            fmlas.add(tuple2Expr(origModelForTupleGeneration, leftTupleContext).in(x.left));
            fmlas.add(tuple2Expr(origModelForTupleGeneration, rightTupleContext).in(x.right));
            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, fmlas);
            debug("Product expression "+x+" desugared to "+desugared, x);
            return desugared.accept(this);     

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
            return x.left.gt(x.right).not().accept(this);
        } else if(x.op.equals(ExprBinary.Op.NOT_LT)) {
            return x.left.lt(x.right).not().accept(this);
        } else if(x.op.equals(ExprBinary.Op.NOT_GTE)) {
            return x.left.gte(x.right).not().accept(this);
        } else if(x.op.equals(ExprBinary.Op.NOT_LTE)) {
            return x.left.lte(x.right).not().accept(this);                
        }  else if(x.op.equals(ExprBinary.Op.GT) ||
                x.op.equals(ExprBinary.Op.LT) ||
                x.op.equals(ExprBinary.Op.LTE) ||
                x.op.equals(ExprBinary.Op.GTE)) {
            // Supported numeric binary operators. 
            // For *literal* provenance generation, explain equality on both sides
            int leftVal = AmalgamEvalVisitor.extractIntFromTupleSet(model.eval(x.left));
            //int rightVal = AmalgamEvalVisitor.extractIntFromTupleSet(model.eval(x.right));
            Tuple leftValTup = AmalgamEvalVisitor.buildIntTuple(model, leftVal);
            //Tuple rightValTup = AmalgamEvalVisitor.buildIntTuple(model, rightVal);
            Tuple oldContext = this.currentTupleIfAtomic;
            this.currentTupleIfAtomic = leftValTup;
            ProvenanceTree leftTree = x.left.accept(this);
            this.currentTupleIfAtomic = leftValTup;
            ProvenanceTree rightTree = x.left.accept(this);
            this.currentTupleIfAtomic = oldContext;
            List<ProvenanceTree> lst = new ArrayList<ProvenanceTree>(2);
            lst.add(leftTree);
            lst.add(rightTree);
            return ProvenanceNode.construct(ProvenanceNode.Op.PAND, x, currentSign, lst);
             
        } else if(x.op.equals(ExprBinary.Op.DIV) ||
                x.op.equals(ExprBinary.Op.REM) ||
                x.op.equals(ExprBinary.Op.MUL) ||                    
                x.op.equals(ExprBinary.Op.IPLUS) ||
                x.op.equals(ExprBinary.Op.IMINUS) ||
                x.op.equals(ExprBinary.Op.SHA) ||
                x.op.equals(ExprBinary.Op.SHL) ||
                x.op.equals(ExprBinary.Op.SHR)) {
            // Special error message the indicates this failure is due to numerics
            throw new ErrorFatal("Numeric binary operator "+x.op+" is unsupported in amalgam (literal provenance visitor): "+x);
        }                       
        else                
            throw new ErrorFatal("Unsupported binary op: "+x);
    }

    private void mustHaveTupleContext(Expr x) throws Err {
        if(currentTupleIfAtomic == null)
            throw new ErrorFatal("Relational expression had no tuple context: "+x);
    }

    @Override
    public ProvenanceTree visit(ExprList x) throws Err {
        protectAndError(x);
        debug("Visiting ExprList expression: "+x, x);       

        if(x.op == ExprList.Op.TOTALORDER)
            return AmalgamVisitorHelper.desugarTOTALORDER(x).accept(this);
        
        List<ProvenanceTree> subs = new ArrayList<ProvenanceTree>();
        // a1 /\ ... /\ an    --- all ai that pass cause the fmla to pass
        if(isANDContext(x, currentSign)) { 
            for(Expr e : x.args) {
                boolean res = (Boolean)model.eval(e);
                if(res == currentSign) subs.add(e.accept(this));
                // should never be false?
                //else throw new ErrorFatal("Tried justifying a conjunction with false subexpr: "+e);
            }
            // should never be empty
            if(subs.isEmpty()) {
                throw new ErrorFatal("Empty subs in Ground Visitor for ExprList (AND context): "+x);                
            }
            ProvenanceTree result = ProvenanceNode.construct(ProvenanceNode.Op.PAND, x, currentSign, subs);
            debug("  ~~~  AND context produced provenance tree: "+result, x);
            return result;                
        }
        // a1 \/ ... \/ an \/ b1 \/ ... \/ bn -- any ai that pass cause the fmla to pass
        else if(isORContext(x, currentSign)) {
            for(Expr e : x.args) {
                boolean res = (Boolean)model.eval(e);
                // If sign=true and this subfmla is true, it is responsible
                // If sign=false and this subfmla is false, it is responsible (for violating the syntactic AND)
                if(res == currentSign) subs.add(e.accept(this));
                if(!subs.isEmpty() && nobranch) break;
            }
            // should never be empty
            if(subs.isEmpty()) {
                throw new ErrorFatal("Empty subs in Ground Visitor for ExprList (OR context): "+x);
            }
            ProvenanceTree result = ProvenanceNode.construct(ProvenanceNode.Op.POR, x, currentSign, subs);
            debug("  ~~~  OR context produced provenance tree: "+result, x);
            return result;
        }
        else throw new ErrorFatal("Unsupported nary op: "+x);
    }

    @Override
    public ProvenanceTree visit(ExprCall x) throws Err {
        protectAndError(x);
        debug("Visiting ExprCall expression: "+x, x);        
        return AmalgamVisitorHelper.resolveExprCall(x).accept(this);        
    }

    @Override
    public ProvenanceTree visit(ExprConstant x) throws Err {
        protectAndError(x);
        debug("Visiting ExprConstant expression: "+x, x);
        // Can never differ, but might be an antecedent in an explanation...
        // If this is an *expression*, use currentTuple. Otherwise, just use x.
        Expr ground;
        // N.b., can't do ExprConstant.TRUE.equals...; only the *op* is canonical
        if(ExprConstant.Op.TRUE.equals(x.op) || ExprConstant.Op.FALSE.equals(x.op)) {
            ground = x;
        } else {
            ground = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x);        
        }    
        if(!currentSign) ground = ground.not();  
        return new ProvenanceLeaf(ground);                       
    }

    @Override
    public ProvenanceTree visit(ExprITE x) throws Err {
        protectAndError(x);
        // if C do X else Y
        debug("Visiting ExprITE expression: "+x, x);
        Expr desugared = x.cond.and(x.left).or(x.cond.not().and(x.right));                        
        return desugared.accept(this);
    }

    @Override
    public ProvenanceTree visit(ExprLet x) throws Err {
        protectAndError(x);
        debug("Visiting ExprLet expression: "+x, x);
        //    Substitute the let variable in the subexpression
        Expr desugared = x.sub.accept(new AmalgamSubstituteVisitor(x.var, x.expr, false));
        return desugared.accept(this);               
    }

    @Override
    public ProvenanceTree visit(ExprQt x) throws Err {
        protectAndError(x);
        debug("Visiting ExprQt expression: "+x+"; decls size="+x.decls.size(), x);
        if(x.decls.size() > 0) {
            debug("    First decl had expr="+x.decls.get(0).expr, x);
        }
        if(x.op.equals(ExprQt.Op.COMPREHENSION)) {
            return AmalgamVisitorHelper.desugarComprehension(origModelForTupleGeneration, x, currentTupleIfAtomic).accept(this);
        } else if(x.op.equals(ExprQt.Op.SUM)) {
            return visitSum(x);
        } else {
            Expr desugared = desugarQuantifier(x);
            if(desugared instanceof ExprQt)
                return visitQuantifier((ExprQt)desugared);
            else
                return desugared.accept(this);
        }              
    }

    private ProvenanceTree visitSum(ExprQt x) throws Err {        
        throw new ErrorFatal("sum not yet supported by Amalgam"); 
    }    

    private ProvenanceTree visitQuantifier(ExprQt x) throws Err {
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
        TupleSet upperBoundInstantiations = T.accept(new AmalgamUpperBoundVisitor(root, model));        

        // all v: T | F(x) 
        //    ~~> T(t1) => F(t1) /\ ...
        // some v: T | F(x) 
        //    ~~> T(t1) /\ F(t1) \/ ...

        List<Expr> subExprs = new ArrayList<Expr>();        

        for(Tuple tup : upperBoundInstantiations) {           
            // Substitute <instantation> for <v>
            Expr instantiation = tuple2Expr(origModelForTupleGeneration, tup);
            Expr substituted = x.sub.accept(new AmalgamSubstituteVisitor(v, instantiation, false));      
            debug("SUBSTITUTING: "+v+" ~> "+instantiation+". Produced "+substituted, x);

            Expr qinst;
            if(x.op.equals(ExprQt.Op.ALL)) 
                qinst = instantiation.in(T).not().or(substituted);
            else if(x.op.equals(ExprQt.Op.SOME)) 
                qinst = instantiation.in(T).and(substituted);
            else
                throw new ErrorFatal("Unknown quantifier type in ground visitor (after desugaring): "+x.op);

            // (Remember, all/some here is in context of sign)
            // If "all", this qinst must be true in model. SOME qinst is false in model.
            // If "some", this qinst  must be false in model. SOME qinst is true in model.

            subExprs.add(qinst);
        }
        Expr desugared = ExprList.make(x.pos, x.closingBracket, (x.op.equals(ExprQt.Op.ALL) ? ExprList.Op.AND : ExprList.Op.OR), subExprs);        
        return desugared.accept(this);        
    }

    @Override
    public ProvenanceTree visit(ExprUnary x) throws Err {
        protectAndError(x);
        debug("Visiting ExprUnary (op="+x.op+") expression: "+x, x);
        ProvenanceTree result = null;
        if(x.op.equals(ExprUnary.Op.NOOP)) {
            return x.sub.accept(this);
        }
        
        // casts are effectively no-ops for integers
        else if(x.op.equals(ExprUnary.Op.CAST2INT) ||
                x.op.equals(ExprUnary.Op.CAST2SIGINT)) {
            return x.sub.accept(this);
        }

        
        else if(x.op.equals(ExprUnary.Op.CARDINALITY)) {
            // Note how different this is from the EvalVisitor version! We just need to know why {tuple} in x.sub. 
            // but in this case, {tuple} is a singleton integer and we need to say how to evaluate the # operator. 
            // In fact, here we don't even need to know what {tuple} is for positive case
            // (n.b. we _do_ in other kinds of int expressions).                         
            
            TupleSet ub = x.sub.accept(new AmalgamUpperBoundVisitor(root, model));            
            A4TupleSet contents = (A4TupleSet) model.eval(x.sub);
            
            if(AmalgamVisitorHelper.debugGround) {
                int nValue = (Integer)model.eval(x);
                if(contents.size() != nValue) {
                    throw new ErrorFatal("Cardinality had unexpected evaluation: "+nValue+" from evaluating #; inner expression: "+contents.size());
                }
                if(AmalgamVisitorHelper.sanityCheck) {
                    int fValue = (Integer)origModelForTupleGeneration.eval(x);
                    if(fValue != nValue) {
                        throw new ErrorFatal("Value of "+x+" differed across models: orig:"+fValue+" flipped:"+nValue);
                    }
                }                
            }
            
            List<ProvenanceTree> subTrees = new ArrayList<ProvenanceTree>(ub.size());
            for(Tuple t : ub) {                    
                Expr texpr = AmalgamVisitorHelper.tuple2Expr(origModelForTupleGeneration, t);
                boolean inModel = contents.debugGetKodkodTupleset().contains(t);                
                           
                debug("cardinality processing tuple:"+t+"; inModel="+inModel+":", x);
                
                // If currentSign = true, we are explaining why the expression has the cardinality it does.
                // If currentSign = false, we are explaining why it does _not_ evaluate to {val}. Which should be same as above. 
                //   However, we're now in a *positive* context for each tuple check. 
                
                boolean oldSign = this.currentSign;
                this.currentSign = true;
                if(inModel) {              
                    subTrees.add(texpr.in(x.sub).accept(this)); // XXX not quite right
                } else {
                    subTrees.add(texpr.in(x.sub).not().accept(this));
                }
                this.currentSign = oldSign;
            }
            
            return ProvenanceNode.construct(ProvenanceNode.Op.PAND, x, currentSign, subTrees);
        }
        
        // *********************************
        // Boolean unary operators
        // *********************************
        // Flip sign of context if needed
        else if(x.op.equals(ExprUnary.Op.NOT)) {
            currentSign = !currentSign;
            result = x.sub.accept(this);
            currentSign = !currentSign;
        } 
        else if(x.op.equals(ExprUnary.Op.SOME)) {
            // XXX TN: see AmalgamEvalVisitor for comments. Duplicate code.
            TupleSet upperBoundInstantiations = x.sub.accept(new AmalgamUpperBoundVisitor(root, model));
            if(upperBoundInstantiations.size() < 1) {
             //   throw new ErrorFatal("Literal Eval on some E but E had empty upper bound");
                if(currentSign) return new ProvenanceConstantLeaf(ProvenanceConstantLeaf.TYPE.TRUE_WRT_BOUNDS, x);
                else return new ProvenanceConstantLeaf(ProvenanceConstantLeaf.TYPE.FALSE_WRT_BOUNDS, x);
            }

            List<Expr> subFmlas = new ArrayList<Expr>(); 
            for(Tuple instantiation : upperBoundInstantiations) {
                Expr tup = tuple2Expr(origModelForTupleGeneration, instantiation);
                subFmlas.add(tup.in(x.sub));
            }

            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, subFmlas);                                               
            return desugared.accept(this);
        }
        else if(x.op.equals(ExprUnary.Op.LONE)) {
            // desugar as one or no
            return x.sub.one().or(x.sub.no()).accept(this);
        }
        else if(x.op.equals(ExprUnary.Op.ONE)) {
            // XXX TN: see AmalgamEvalVisitor for comments. Duplicate code.
            TupleSet upperBoundInstantiations = x.sub.accept(new AmalgamUpperBoundVisitor(root, model));
            if(upperBoundInstantiations.size() < 1) {
                //throw new ErrorFatal("Literal Eval on some E but E had empty upper bound");
                if(currentSign) return new ProvenanceConstantLeaf(ProvenanceConstantLeaf.TYPE.TRUE_WRT_BOUNDS, x);
                else return new ProvenanceConstantLeaf(ProvenanceConstantLeaf.TYPE.FALSE_WRT_BOUNDS, x);
            }

            List<Expr> subFmlas = new ArrayList<Expr>(); 
            for(Tuple instantiation : upperBoundInstantiations) {
                Expr tup = tuple2Expr(origModelForTupleGeneration, instantiation);
                List<Expr> uniques = new ArrayList<Expr>();

                // ...and none of the other tuples are in the expression
                for(Tuple other : upperBoundInstantiations) {
                    if(other.equals(instantiation)) continue;
                    Expr tup2 = tuple2Expr(origModelForTupleGeneration, other);
                    Expr unique = tup2.in(x.sub).not();
                    uniques.add(unique);
                }                    
                Expr uniqueness = ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, uniques);                     
                subFmlas.add(tup.in(x.sub).and(uniqueness));
            }

            Expr desugared = ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, subFmlas);                                               
            return desugared.accept(this);               
        }            
        else if(x.op.equals(ExprUnary.Op.NO)) {
            // desugar as not some
            Expr desugared = x.sub.some().not();
            return desugared.accept(this);
        }
        // *********************************
        // Relational unary operators
        // *********************************
        // SETOF is vaguely like a no-op in this context. inserted by type decl fmla building
        // Note that this assumes a tuple context is present! So we are evaluating something like
        // Node$1->Node$2 in set this/Node. Treating this as a NOOP in a quantifier Decl would be unsafe. 
        else if(x.op.equals(ExprUnary.Op.SETOF)) {                
            return x.sub.accept(this);
        }
        else if(x.op.equals(ExprUnary.Op.CLOSURE)) {
            // Desugar as (potentially massive) disjunction. Enumerate all paths in upper bound.
            mustHaveTupleContext(x);

            if(currentTupleIfAtomic.arity() != 2) 
                throw new ErrorFatal("Tried to compute closure with non-binary tuple context: "+currentTupleIfAtomic);                
            Object source = currentTupleIfAtomic.atom(0);
            Object destination = currentTupleIfAtomic.atom(1);

            TupleSet ub = x.sub.accept(new AmalgamUpperBoundVisitor(root, model));

            // For <s,d> to be in ^sub, one of the possible paths has to be there.
            Set<List<Object>> spaths = buildSimplePaths(source, destination, ub, new HashSet<Object>());


            List<Expr> possibilities = new ArrayList<Expr>();
            for(List<Object> apath : spaths) {
                Expr possibility = null;
                for(int ii=0;ii<apath.size()-1;ii++) {
                    // for each edge taken in this path
                    Tuple thop = model.getFactory().tuple(apath.get(ii), apath.get(ii+1));                        
                    Expr ehop = tuple2Expr(origModelForTupleGeneration, thop);                        
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
            result = desugared.accept(this);
            currentTupleIfAtomic = saveTuple;
            return result;
        }
        else if(x.op.equals(ExprUnary.Op.RCLOSURE)) {
            mustHaveTupleContext(x);
            // sugar
            Expr desugared = ExprConstant.IDEN.plus(x.sub.closure());
            return desugared.accept(this); // same context tuple
        }
        else if(x.op.equals(ExprUnary.Op.TRANSPOSE)) {
            mustHaveTupleContext(x);
            // flip the context tuple
            Tuple saveTuple = currentTupleIfAtomic;
            currentTupleIfAtomic = transposeTuple(model, currentTupleIfAtomic);
            result = x.sub.accept(this);
            currentTupleIfAtomic = saveTuple;
            return result;
        }
        else throw new ErrorFatal("Unsupported unary operator: "+x.op+" in "+x);
        return result;
    }

    @Override
    public ProvenanceTree visit(ExprVar x) throws Err {
        protectAndError(x);
        debug("Visiting ExprVar expression: "+x, x);
        // If quantified variable, will be substituted out. If a let, should be resolved out. 
        // Otherwise it's something understandable at top level.
        // This must *fail*, and in tuple context.
        Expr ground = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x);
        if(!currentSign) ground = ground.not();  
        return new ProvenanceLeaf(ground);
    }

    @Override
    public ProvenanceTree visit(Sig x) throws Err {
        protectAndError(x);
        if(currentTupleIfAtomic == null)
            throw new ErrorFatal("Had no tuple context when diff evaluating "+x);

        debug("Visiting Sig expression: "+x+" (tup context="+currentTupleIfAtomic+")", x);
        //debug("    flipTup="+flipTup+"; flipRel="+flipRel);
        //debug("    flipTup==context="+flipTup.equals(currentTupleIfAtomic)+"; flipRel==context="+flipRel.equals(x));
        // This must *fail*, and in tuple context.
        // XXX no failures should happen in a justification?
        //        if(flipTup.equals(currentTupleIfAtomic) && flipRel.equals(x))
        //            return new ProvenanceContradiction();        
        Expr ground = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x);
        if(!currentSign) ground = ground.not();  
        return new ProvenanceLeaf(ground);
    }

    @Override
    public ProvenanceTree visit(Field x) throws Err {
        protectAndError(x);
        if(currentTupleIfAtomic == null)
            throw new ErrorFatal("Had no tuple context when diff evaluating "+x);

        debug("Visiting Field expression: "+x+" (tup context="+currentTupleIfAtomic+")", x);
        // This must *fail*, and in tuple context.
        // XXX no failures should happen in a justification?
        //        if(flipTup.equals(currentTupleIfAtomic) && flipRel.equals(x))
        //            return new ProvenanceContradiction();        
        Expr ground = tuple2Expr(origModelForTupleGeneration, currentTupleIfAtomic).in(x);       
        if(!currentSign) ground = ground.not();  
        return new ProvenanceLeaf(ground);
    }

}

