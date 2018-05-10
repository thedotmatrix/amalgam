package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.WrappedExpr2;

public class ProvenanceTraceWrapper {

    final ProvenanceTrace trace;
    final List<TopLevelWrappedExpr> alphaSkeletons;
    //final List<TopLevelWrappedExpr> failureSkeletons;
    final boolean sign;
    public boolean isDisabled = false;
    
    public ProvenanceTraceWrapper(ProvenanceTrace trace, CoverageExpansionVisitor expander, boolean sign) {
        this.trace = trace;
        this.sign = sign;
        
        List<ProvenanceLeaf> alphas = trace.getAlphas();
        List<TopLevelWrappedExpr> alphaList = new ArrayList<>(alphas.size());
        for (ProvenanceLeaf a : alphas) {
            alphaList.add(new TopLevelWrappedExpr(a, expander));
        }
        Collections.sort(alphaList);
        this.alphaSkeletons = Util.dedup(alphaList);
        
        /*
        Set<Expr> failures = trace.getLeafFailures();
        List<TopLevelWrappedExpr> failureList = new ArrayList<>(failures.size());
        for (final Expr a : failures) {
            ExprContainer e = new ExprContainer() {
                @Override
                public Expr getContents() {
                    return a;
                }
            };
            failureList.add(new TopLevelWrappedExpr(e, null));
        }
        Collections.sort(failureList);
        this.failureSkeletons = Util.dedup(failureList);
        */
    }
    
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((alphaSkeletons == null) ? 0 : alphaSkeletons.hashCode());
        //result = prime * result + ((failureSkeletons == null) ? 0 : failureSkeletons.hashCode());
        result = prime * result + (sign ? 1231 : 1237);
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        ProvenanceTraceWrapper other = (ProvenanceTraceWrapper) obj;
        if (alphaSkeletons == null) {
            if (other.alphaSkeletons != null)
                return false;
        } else if (!alphaSkeletons.equals(other.alphaSkeletons))
            return false;
        /*
        if (failureSkeletons == null) {
            if (other.failureSkeletons != null)
                return false;
        } else if (!failureSkeletons.equals(other.failureSkeletons))
            return false;
        */
        if (sign != other.sign)
            return false;
        return true;
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("(ProvenanceSkeleton\n#:alphas (list\n");
        for (TopLevelWrappedExpr a : alphaSkeletons) {
            sb.append(a + "\n");
        }
        /*
        sb.append(")\n#:failures (list\n");
        for (TopLevelWrappedExpr a : failureSkeletons) {
            sb.append(a + "\n");
        }
        */
        sb.append(")\n#:sign " + sign + ")");
        return sb.toString();
    }

    public ProvenanceTrace getTrace() {
        return trace;
    }

    public boolean getSign() {
        return sign; // to aid debugging
    }
    
    public boolean isSubsumedBy(ProvenanceTraceWrapper b) {
        if (! ((sign == b.sign) /* && failureSkeletons.equals(b.failureSkeletons) */)) return false;
        
        for (TopLevelWrappedExpr alphaSkeleton : alphaSkeletons) {
            boolean check = false;
            WrappedExpr2 alpha = alphaSkeleton.skeleton;
            for (TopLevelWrappedExpr bAlphaSkeleton : b.alphaSkeletons) {
                WrappedExpr2 beta = bAlphaSkeleton.skeleton;
                if (alpha.e2.getContent().isSubsumedBy(
                        beta.e2.getContent())) {
                    check = true;
                    break;
                }
                
            }
            if (!check) return false;
        }
        return true;
    }
}
