package edu.mit.csail.sdg.alloy4compiler.ast;

public class WrappedExpr2 implements Comparable<WrappedExpr2> {
    // COULD BE NULL
    final public WrappedExpr e1, e2, e3;
    
    public WrappedExpr2(WrappedExpr e1, WrappedExpr e2, WrappedExpr e3) {
        this.e1 = e1;
        this.e2 = e2;
        this.e3 = e3;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((e1 == null) ? 0 : e1.hashCode());
        result = prime * result + ((e2 == null) ? 0 : e2.hashCode());
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
        WrappedExpr2 other = (WrappedExpr2) obj;
        if (e1 == null) {
            if (other.e1 != null)
                return false;
        } else if (!e1.equals(other.e1))
            return false;
        if (e2 == null) {
            if (other.e2 != null)
                return false;
        } else if (!e2.equals(other.e2))
            return false;
        return true;
    }

    @Override
    public int compareTo(WrappedExpr2 o) {
        if (e1 == null && o.e1 != null) return -1;
        if (e1 != null && o.e1 == null) return 1;
        
        int result = 0;
        if (e1 != null && o.e1 != null) {
            result = e1.compareTo(o.e1);
        }
        
        if (result != 0) return result;
        if (e2 == null && o.e2 == null) return 0;
        if (e2 == null && o.e2 != null) return -1;
        if (e2 != null && o.e2 == null) return 1;
        result = e2.compareTo(o.e2);
        if (result != 0) return result;
        return 0;
    }

    @Override
    public String toString() {
        return "(WrappedExpr2\n#:e1 " + e1 + "\n#:e2 " + e2 + "\n#:e3 " + e3 + ")";
    }
}