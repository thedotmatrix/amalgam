package edu.mit.csail.sdg.alloy4compiler.translator;

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

public class AmalgamUpperBoundVisitor extends VisitReturn<TupleSet> {                 
    final A4Solution soln;
    final Module root;   
              
    public AmalgamUpperBoundVisitor(Module root, A4Solution soln) {
        this.soln = soln;        
        this.root = root; 
    }
    
    public void debug(String msg) {
        if(AmalgamVisitorHelper.debugUB) System.err.println("########## Amalgam UPPER-BOUND Visitor Debug: "+msg);
    }
         
    public String getOperatorInfo(Expr x) {
        if(x instanceof ExprUnary) {
            return ((ExprUnary) x).op.toString();
        } else if (x instanceof ExprBinary) {
            return ((ExprBinary) x).op.toString();
        }
        return "UNKNOWN OPERATOR";
    }
    
    private TupleSet err(Expr x) throws Err {
        throw new ErrorFatal("AmalgamUpperBoundVisitor called on non-relational (or unsupported) expression: "+x+": "+getOperatorInfo(x));
    }
    
    @Override
    public TupleSet visit(ExprBinary x) throws Err {
        debug("Visiting ExprBinary (op="+x.op+") expression: "+x);

        TupleSet leftBounds = x.left.accept(this);
        TupleSet rightBounds = x.right.accept(this);           
           
        if(x.op.equals(ExprBinary.Op.PLUS)) { 
            TupleSet result = new TupleSet(leftBounds.universe(), leftBounds.arity());
            result.addAll(leftBounds);
            result.addAll(rightBounds);
            return result; 
        }
        else if(x.op.equals(ExprBinary.Op.INTERSECT)) { 
            TupleSet result = new TupleSet(leftBounds.universe(), leftBounds.arity());
            result.addAll(leftBounds);
            result.retainAll(rightBounds); 
            return result;           
        }
        else if(x.op.equals(ExprBinary.Op.MINUS)) { 
            TupleSet result = new TupleSet(leftBounds.universe(), leftBounds.arity());
            result.addAll(leftBounds);
            // Don't confuse semantics with upper bounds. 
            // Upper bound of A-B is A's upper bound (in case B empty).
            return result; 
        }
        else if(x.op.equals(ExprBinary.Op.PLUSPLUS)) { 
            // same as union
            TupleSet result = new TupleSet(leftBounds.universe(), leftBounds.arity());
            result.addAll(leftBounds);
            result.addAll(rightBounds);
            return result;  
        }
        else if(x.op.equals(ExprBinary.Op.DOMAIN)) { 
            // RHS contains set we're removing from
            TupleSet result = new TupleSet(rightBounds.universe(), rightBounds.arity());
            result.addAll(rightBounds);
            return result; 
        }
        else if(x.op.equals(ExprBinary.Op.RANGE)) { 
            // LHS contains set we're removing from
            TupleSet result = new TupleSet(leftBounds.universe(), leftBounds.arity());
            result.addAll(leftBounds); 
            return result; 
        }    
        else if(x.op.equals(ExprBinary.Op.ARROW)) { 
            // product of tuple sets
            return leftBounds.product(rightBounds);            
        }    
        else if(x.op.equals(ExprBinary.Op.JOIN)) {
            // Not Project(A, 1..n-1) X Project(B, 2..m). This is too permissive.
            // Instead, build tuple by tuple.
            TupleSet result = new TupleSet(rightBounds.universe(), leftBounds.arity()+rightBounds.arity()-2);
            for(Tuple lt : leftBounds) {                
                for(Tuple rt : rightBounds) {
                    Tuple newT = AmalgamVisitorHelper.joinTuple(soln, lt, rt);                    
                    if(newT != null) result.add(newT);
                }
            }
            debug("    (UB) join: "+x.left+" "+leftBounds+" | "+x.right+" "+rightBounds+"  => "+result);
            return result;
        }  

        else {
            return err(x);
        }                    
    }

    @Override
    public TupleSet visit(ExprList x) throws Err {
        return err(x);
    }

    @Override
    public TupleSet visit(ExprCall x) throws Err {
        debug("Visiting ExprCall expression: "+x);
        return AmalgamVisitorHelper.resolveExprCall(x).accept(this); 
    }

    @Override
    public TupleSet visit(ExprConstant x) throws Err {
        debug("Visiting ExprConstant expression: "+x);        
        if(x.op.equals(ExprConstant.Op.IDEN)) {  
            // The upper bound of IDEN is all pairs over everything, even the un-used atoms (because upper bound)
            TupleSet idenIs = new TupleSet(soln.getBounds().universe(), 2);
            for(int i = 0; i<soln.getBounds().universe().size();i++) {
                Object a = soln.getBounds().universe().atom(i);
                Tuple t = soln.getBounds().universe().factory().tuple(a, a);
                idenIs.add(t);
            }
            return soln.getBounds().universe().factory().allOf(2);            
        } else if(x.op.equals(ExprConstant.Op.EMPTYNESS)) {       
            // The upper bound of emptiness is always empty
            return soln.getBounds().universe().factory().noneOf(2);
        } else if(x.op.equals(ExprConstant.Op.NUMBER)) {
            //System.err.println("num for exprconstant: "+x.num+" has bound "+soln.getBounds().exactBound(x.num));
            return soln.getBounds().exactBound(x.num);
        } else if(x.op.equals(ExprConstant.Op.NEXT)) { // integer successor
            A4TupleSet res = (A4TupleSet)soln.eval(x);            
            return res.debugGetKodkodTupleset();
        } else
            return err(x);
        
        // TODO are we missing univ, here?
        
    }

    @Override
    public TupleSet visit(ExprITE x) throws Err {
        return err(x);               
    }

    @Override
    public TupleSet visit(ExprLet x) throws Err {        
        return err(x);         
    }

    @Override
    public TupleSet visit(ExprQt x) throws Err {
        debug("Visiting ExprQt expression: "+x);
           
        if(x.op.equals(ExprQt.Op.COMPREHENSION)) {
            return visitComprehension(x);
        } else
            return err(x); 
    }        

    /*
    private TupleSet visitSum(ExprQt x) throws Err {
        return err(x); 
    }
    */

    private TupleSet visitComprehension(ExprQt x) throws Err {
        // Don't know arity until we measure XXX: starting with 1 might be an issue?
        TupleSet result = null;
        
        //System.err.println("upper bound visitor in comprehension: "+x);
        
        // Product all decls
        for(Decl d : x.decls) {
            for(@SuppressWarnings("unused") ExprHasName n : d.names) {
                if(result == null) result = d.expr.accept(this);
                else result = result.product(d.expr.accept(this));
                //System.err.println("result: "+result);                
            }
        }
        return result;              
    }    
    
    @Override
    public TupleSet visit(ExprUnary x) throws Err {
        debug("Visiting ExprUnary (op="+x.op+") expression: "+x);        
        TupleSet subBounds = x.sub.accept(this);
        
        if(x.op.equals(ExprUnary.Op.NOOP)) {
            return x.sub.accept(this);
        }        
        if(x.op.equals(ExprUnary.Op.ONEOF)) {
            // any other multiplicity should be rejected (higher-order or lone)
            return x.sub.accept(this);
        }
        if(x.op.equals(ExprUnary.Op.TRANSPOSE)) {
            // transpose the bounds themselves
            TupleSet result = new TupleSet(subBounds.universe(), subBounds.arity());
            for(Tuple t : subBounds) {
                if(t.arity() != 2) throw new ErrorFatal("computing upper bounds for "+x+"; got non binary tuple: "+t);
                result.add(soln.getFactory().tuple(t.atom(1), t.atom(0)));
            }
            return result;
        } 
        else if(x.op.equals(ExprUnary.Op.CLOSURE)) {
            // generate transitive closure of bounds
            return AmalgamVisitorHelper.buildClosureOfTupleSet(soln, subBounds);           
        }
        else if(x.op.equals(ExprUnary.Op.RCLOSURE)) {
            // CLOSURE case plus IDEN
            // Note that IDEN is identity on all used atoms, not just subBounds, and so
            // we need to add identity over all possible atoms            
            TupleSet idenIs = (TupleSet) ExprConstant.IDEN.accept(this);                        
            TupleSet result = new TupleSet(subBounds.universe(), subBounds.arity());
            result.addAll(AmalgamVisitorHelper.buildClosureOfTupleSet(soln, subBounds));                                                
            result.addAll(idenIs);
            return result;
        } 
        else if(x.op.equals(ExprUnary.Op.CAST2INT)) {
            return x.sub.accept(this);
        }
        else if(x.op.equals(ExprUnary.Op.CAST2SIGINT)) {
            return x.sub.accept(this);
        }                
        else {            
            return err(x);
        }
    }
      
    @Override
    public TupleSet visit(ExprVar x) throws Err {
        debug("Visiting ExprVar expression: "+x+"; soln.a2k returned: "+soln.a2k(x));
        // This should be a constant variable like Node$0; map correctly
        Object res = soln.eval(x);
        if(!(res instanceof A4TupleSet)) 
            throw new ErrorFatal("Evaluation of ExprVar in UpperBounds visitor did not return an A4TupleSet: "+x+" ~> "+res);
        TupleSet tsetres = ((A4TupleSet)res).debugGetKodkodTupleset();
        if(tsetres.size() > 1) 
            throw new ErrorFatal("Evaluation of ExprVar UpperBounds visitor produced set of size >1: "+x+" ~> "+tsetres);
        return tsetres;  
    }

    @Override
    public TupleSet visit(Sig x) throws Err {
        debug("Visiting Sig expression: "+x);
        return soln.query(true, soln.a2k(x), false); 
    }

    @Override
    public TupleSet visit(Field x) throws Err {
        debug("Visiting Field expression: "+x);
        return soln.query(true, soln.a2k(x), false);        
    }
 
}
