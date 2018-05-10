package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;

public class AmalgamTupleInExpr {
    public Expr e;
    public A4Tuple t;
    public boolean sign; // was this test removing (true) or adding (false) this tuple?
    
    // For fields of "one" sigs, Alloy doesn't pass the leftmost column to Kodkod at all.
    public boolean isTruncatedOne; 
    
    AmalgamTupleInExpr(Expr e, A4Tuple t, boolean trunc, boolean sign) {
        this.e = e;
        this.t = t;
        this.isTruncatedOne = trunc;
        this.sign = sign;
    }
    
    public String toString() {
        return (sign ? "+" : "-") + e.toString() + "(" +t.toString() + ")" + (isTruncatedOne ? "[-one]" : "");
    }
}