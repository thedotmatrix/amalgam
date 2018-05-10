package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprITE;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprLet;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprQt;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;
import edu.mit.csail.sdg.alloy4compiler.ast.WrappedExpr;

public class CoverageCanonicalizerVisitor extends VisitReturn<Expr> {
    
    @Override
    public Expr visit(ExprBinary x) throws Err {
        return (ExprBinary) x.op.make(x.pos, x.closingBracket, x.left.accept(this), x.right.accept(this));
    }

    @Override
    public Expr visit(ExprList x) throws Err {
        // collapse desugaring from transitive closure and quantifier by 
        // unifying those expression with same srcloc and skeleton
        Set<WrappedExpr> args = new HashSet<>(x.args.size());
        for(Expr e : x.args) {
            args.add(new WrappedExpr(e.accept(this)));
        }
        List<Expr> realArgs = new ArrayList<>(args.size());
        for (WrappedExpr e : args) {
            realArgs.add(e.getContent());
        }
        Collections.sort(realArgs);
        return ExprList.make(x.pos, x.closingBracket, x.op, realArgs);
    }

    @Override
    public Expr visit(ExprCall x) throws Err {
        List<Expr> args = new ArrayList<Expr>(x.args.size());            
        for(Expr arg : x.args) {
            Expr newArg = arg.accept(this);
            args.add(newArg);
        }
        return ExprCall.make(x.pos, x.closingBracket, x.fun, args, x.extraWeight);
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {
        if (x.op.equals(ExprConstant.Op.NUMBER)) {
            return  ExprConstant.Op.NUMBER.make(x.pos, 0);
        }
        return x;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {
        return (ExprITE) ExprITE.make(x.pos, x.cond.accept(this), x.left.accept(this), x.right.accept(this));
    }

    @Override
    public Expr visit(ExprLet x) throws Err {
        return (ExprLet)ExprLet.make(x.pos, x.var, x.expr.accept(this), x.sub.accept(this));
    }

    @Override
    public Expr visit(ExprQt x) throws Err {
        List<Decl> decls = new ArrayList<Decl>(x.decls.size());
        for(Decl d : x.decls) {
            decls.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, d.names, d.expr.accept(this)));            
        }
        return (ExprQt) x.op.make(x.pos, x.closingBracket, decls, x.sub.accept(this));
    }

    @Override
    public Expr visit(ExprUnary x) throws Err {
        return (ExprUnary) x.op.make(x.pos, x.sub.accept(this));
    }

    @Override
    public Expr visit(ExprVar x) throws Err {
        return ExprVar.make(x.pos, x.toString().replaceFirst("^[A-Za-z0-9'\"_/]*\\$\\d+$", "\\$").replaceAll("unused\\d+", "\\$"));
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
