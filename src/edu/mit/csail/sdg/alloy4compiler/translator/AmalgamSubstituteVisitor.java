package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;

public class AmalgamSubstituteVisitor extends VisitReturn<Expr> {
    Map<ExprHasName, Expr> substitutions;
    boolean fullyExpandCalls;
    
    public AmalgamSubstituteVisitor(ExprHasName v, Expr with, boolean fullyExpandCalls) {
        this.substitutions = new HashMap<ExprHasName, Expr>();
        this.substitutions.put(v,  with);
        this.fullyExpandCalls = fullyExpandCalls;
    }
    @SuppressWarnings("unchecked")
    public AmalgamSubstituteVisitor(Map<ExprHasName, ? extends Expr> substitutions, boolean fullyExpandCalls) {
        this.substitutions = (Map<ExprHasName, Expr>)substitutions;
        this.fullyExpandCalls = fullyExpandCalls;
    }    
    
    @Override
    public ExprBinary visit(ExprBinary x) throws Err {                  
        ExprBinary result = (ExprBinary) x.op.make(x.pos, x.closingBracket, x.left.accept(this), x.right.accept(this));
        //System.err.println("~~ Subst: "+x+" --> "+result);
        return result;  
    }

    @Override
    public ExprList visit(ExprList x) throws Err {
        List<Expr> substitutedArgs = new ArrayList<Expr>(x.args.size()); 
        for(Expr arg : x.args) {
            substitutedArgs.add(arg.accept(this));
        }
        ExprList result = ExprList.make(x.pos, x.closingBracket, x.op, substitutedArgs);
        //System.err.println("~~ Subst: "+x+" --> "+result);
        return result;
    }

    @Override
    public Expr visit(ExprCall x) throws Err { 
        // x := myPredOrFunctionReference[myarg1, myarg2, ...]
        // x.fun := myPredOrFunctionReference, {v1, v2, ...}
        if(fullyExpandCalls) {
            // Option 1: substitute *completely*---resolve this inner call, then substitute entire body
            // Do fresh substitution to remove the call, then continue with *this* substitution
            return AmalgamVisitorHelper.resolveExprCall(x).accept(this);
        } else {
            // Option 2: substitute only as far as the call itself. Replace parameters as needed.
            List<Expr> substitutedArgs = new ArrayList<Expr>(x.args.size());            
            for(Expr arg : x.args) {
                Expr newArg = arg.accept(this);
                substitutedArgs.add(newArg);
                //System.err.println("substituted call arg in "+x.fun.label+": "+arg+" -> "+newArg);
            }
            return ExprCall.make(x.pos, x.closingBracket, x.fun, substitutedArgs, x.extraWeight);
        }
    }

    @Override
    public ExprConstant visit(ExprConstant x) throws Err {               
        return x; // nothing to substitute
    }

    @Override
    public ExprITE visit(ExprITE x) throws Err {        
        ExprITE result = (ExprITE) ExprITE.make(x.pos, x.cond.accept(this), x.left.accept(this), x.right.accept(this));
        //System.err.println("~~ Subst: "+x+" --> "+result);
        return result;
    }

    @SuppressWarnings("unlikely-arg-type")
    @Override
    public ExprLet visit(ExprLet x) throws Err {        
        if(this.substitutions.containsKey(x.var.label))
            throw new ErrorFatal("Substitute Visitor arrived at shadowed let expression: "+x);
        return (ExprLet)ExprLet.make(x.pos, x.var, x.expr.accept(this), x.sub.accept(this));           
    }

    @Override
    public ExprQt visit(ExprQt x) throws Err {            
        List<Decl> substitutedDecls = new ArrayList<Decl>(x.decls.size());
        for(Decl d : x.decls) {
            // sanity check for recapture first
            for(ExprHasName v : this.substitutions.keySet()) {
                if(d.names.contains(v)) {
                    throw new ErrorFatal("Substitution tried to replace variable that is quantified in subexpression: "+v);
                }
            }
            substitutedDecls.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, d.names, d.expr.accept(this)));            
        }
        ExprQt result = (ExprQt) x.op.make(x.pos, x.closingBracket, substitutedDecls, x.sub.accept(this));
        //System.err.println("~~ Subst: "+x+" --> "+result);
        return result;
    }

    
    @Override
    public ExprUnary visit(ExprUnary x) throws Err {
        return (ExprUnary) x.op.make(x.pos, x.sub.accept(this));            
    }

    @Override
    public Expr visit(ExprVar x) throws Err {
        if(this.substitutions.containsKey(x)) { // same variable object
            //System.err.println("=== Substituting out variable "+x);
            return this.substitutions.get(x);
        }
            
        return x;            
    }

    @Override
    public Sig visit(Sig x) throws Err {                    
        return x;
    }

    @Override
    public Field visit(Field x) throws Err {     
        // TODO assumes this field isn't the name to substitute
        return x;
    }
      
}
