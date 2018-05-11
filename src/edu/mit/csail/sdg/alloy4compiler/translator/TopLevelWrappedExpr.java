package edu.mit.csail.sdg.alloy4compiler.translator;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.WrappedExpr;
import edu.mit.csail.sdg.alloy4compiler.ast.WrappedExpr2;

public class TopLevelWrappedExpr implements Comparable<TopLevelWrappedExpr> {
    final WrappedExpr2 skeleton;
    
    TopLevelWrappedExpr(ExprContainer p, CoverageExpansionVisitor expander) {
        Expr expr = p.getContents();
        Expr skeletonExpanded = null;
        try {
            if (expander != null) {
                //System.out.println(">>> " + expr);
                skeletonExpanded = expr.accept(expander);
                //System.out.println("<<< " + skeletonExpanded);
                skeletonExpanded = skeletonExpanded.accept(canonicalizerVisitor);
            }
            expr = expr.accept(canonicalizerVisitor);
        } catch (Err e) {
            e.printStackTrace();
        }
        if (expander == null) {
            skeleton = new WrappedExpr2(new WrappedExpr(expr), null, null);
        } else {
            skeleton = new WrappedExpr2(null, new WrappedExpr(skeletonExpanded), null);
        }
    }

    @Override
    public int compareTo(TopLevelWrappedExpr o) {
        return skeleton.compareTo(o.skeleton);
    }
    
    static CoverageCanonicalizerVisitor canonicalizerVisitor = new CoverageCanonicalizerVisitor();
    
    
    @Override
    public String toString() {
        return skeleton.toString();
    }
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        return this.compareTo((TopLevelWrappedExpr) obj) == 0;
    }

    public int hashCode() {
        return skeleton.hashCode();
    }
}
