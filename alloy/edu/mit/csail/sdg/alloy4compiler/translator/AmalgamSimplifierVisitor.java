
package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.List;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
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

/**
 * Visit an Expr and simplify it with respect to orig and flipped.
 * For instance, A or B will return just B if A is false in both models.
 * @author tn
 *
 */
public class AmalgamSimplifierVisitor extends VisitReturn<Expr> {                 
    final A4Solution orig;
    final A4Solution flipped;
    final Module root;    
    private boolean currentSign = true;
    
    public AmalgamSimplifierVisitor(Module root, A4Solution orig, A4Solution flipped) {
        this.orig = orig;
        this.flipped = flipped;
        this.root = root;         
    }
        
    /*
    private boolean evalFormula(A4Solution m, Expr x) throws Err {
        Object result = m.eval(x);
        if(!(result instanceof Boolean)) throw new ErrorFatal("evalFormula expected boolean valued expression: "+x);
        return (Boolean) result;
    }
    */
    
    @Override
    public Expr visit(ExprBinary x) throws Err {        
        //boolean leftOrigVal = evalFormula(orig, x.left);
        //boolean leftFlipVal = evalFormula(flipped, x.left); 
        //boolean rightOrigVal = evalFormula(orig, x.right);
        //boolean rightFlipVal = evalFormula(flipped, x.right);
           
        if(x.op.equals(ExprBinary.Op.OR)) {                        
            return ExprBinary.Op.OR.make(x.pos, x.closingBracket, x.left.accept(this), x.right.accept(this)); 
        }            
        else if(x.op.equals(ExprBinary.Op.AND)) {
            return ExprBinary.Op.AND.make(x.pos, x.closingBracket, x.left.accept(this), x.right.accept(this)); 
        }            
        else if(x.op.equals(ExprBinary.Op.IFF)) {
            return ExprBinary.Op.OR.make(x.pos, x.closingBracket, x.left.accept(this), x.right.accept(this));
        }
        else if(x.op.equals(ExprBinary.Op.IMPLIES)) {
            return ExprBinary.Op.OR.make(x.pos, x.closingBracket, x.left.accept(this), x.right.accept(this));
        }         
        else if(x.op.equals(ExprBinary.Op.IN)) {
            return ExprBinary.Op.IN.make(x.pos, x.closingBracket, x.left.accept(this), x.right.accept(this));
        }
        else if(x.op.equals(ExprBinary.Op.EQUALS)) {            
            return ExprBinary.Op.IN.make(x.pos, x.closingBracket, x.left.accept(this), x.right.accept(this));
        }
        else {
            return x;
        }                    
    }

    @Override
    public Expr visit(ExprList x) throws Err {
        List<Expr> childrenSimplified = new ArrayList<Expr>(x.args.size());
        for(Expr e : x.args) {
            childrenSimplified.add(e.accept(this));
        }
        
        if(x.op.equals(ExprList.Op.OR)) { 
            return ExprList.make(x.pos, x.closingBracket, x.op, childrenSimplified);
        }            
        else if(x.op.equals(ExprList.Op.AND)) 
        {
            return ExprList.make(x.pos, x.closingBracket, x.op, childrenSimplified);
        } else
            throw new ErrorFatal("(alpha-simplification visitor) unsupported ExprList operator: "+x);
    }

    @Override
    public Expr visit(ExprCall x) throws Err {
        return x;
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {        
        return x;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {
        // TODO: simplify?
        return ExprITE.make(x.pos, x.cond, x.left, x.right);               
    }

    @Override
    public Expr visit(ExprLet x) throws Err {        
        return x;        
    }

    @Override
    public Expr visit(ExprQt x) throws Err {         
        if(x.op.equals(ExprQt.Op.COMPREHENSION)) {
            return visitComprehension(x);
        } else if(x.op.equals(ExprQt.Op.SUM)) {
            return visitSum(x);
        } else if(x.op.equals(ExprQt.Op.ALL) || x.op.equals(ExprQt.Op.SOME)) {
            return visitQuantifier(x);
        } else
            throw new ErrorFatal("Qt operator unsupported in simplification: "+x);
    }
            
    private Expr visitSum(ExprQt x) throws Err {
        return x; 
    }

    private Expr visitComprehension(ExprQt x) throws Err {
        return x;               
    }
   
    private Expr visitQuantifier(ExprQt x) throws Err {
        return x;
    }    
    @Override
    public Expr visit(ExprUnary x) throws Err {       
                                
        //Expr subSimplified = x.sub.accept(this);
                           
        if(!x.op.equals(ExprUnary.Op.NOOP))
           return x.sub.accept(this); // disregard NOOP
        
        else if(x.op.equals(ExprUnary.Op.SOME)) {
            return x;
        }
        else if(x.op.equals(ExprUnary.Op.ONE)) {
            return x;
        }
        else if(x.op.equals(ExprUnary.Op.LONE)) {
            return x;
        }
        else if(x.op.equals(ExprUnary.Op.NO)) {
            return x;
        }
        else if(x.op.equals(ExprUnary.Op.CLOSURE)) {
            return x;
        }
        else if(x.op.equals(ExprUnary.Op.RCLOSURE)) {
            return x;
        }
        else if(x.op.equals(ExprUnary.Op.TRANSPOSE)) {
            return x;
        }
               
        else if(x.op.equals(ExprUnary.Op.NOT)) {
            currentSign = !currentSign;
            Expr simplified = x.sub.accept(this);
            currentSign = !currentSign;
            return simplified;
        }
        
        else 
            return x;  
    }

    @Override
    public Expr visit(ExprVar x) throws Err {        
        return x;
    }

    @Override
    public Expr visit(Sig x) throws Err {        
        return x; 
    }

    @Override
    public Expr visit(Field x) throws Err {        
        return x;
    }
 
}
