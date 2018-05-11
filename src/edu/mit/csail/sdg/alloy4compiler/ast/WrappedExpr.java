package edu.mit.csail.sdg.alloy4compiler.ast;

public class WrappedExpr implements Comparable<WrappedExpr> {
    final Expr e;
    
    public WrappedExpr(Expr e) {
        this.e = e;
    }
    
    public Expr getContent() {
        return e;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + e.toString().hashCode();
        //result = prime * result + e.pos().hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "(WrappedExpr " + e.toString() + " #:srcloc " + e.pos().toVeryShortString() + ")"; // change to toString() in production
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        WrappedExpr other = (WrappedExpr) obj;
        return compareTo(other) == 0;
    }

    @Override
    public int compareTo(WrappedExpr o) {
        return e.compareTo(o.e);
    }
}