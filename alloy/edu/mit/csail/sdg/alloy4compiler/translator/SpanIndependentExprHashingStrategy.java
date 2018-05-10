package edu.mit.csail.sdg.alloy4compiler.translator;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import gnu.trove.strategy.*;

@SuppressWarnings("serial")
public class SpanIndependentExprHashingStrategy implements HashingStrategy<Expr> {

    public int computeHashCode(Expr object) {
        return object.spanIndependentHashCode();      
    }

    public boolean equals(Expr o1, Expr o2) { 
        return o1.spanIndependentEquals(o2);     
    }

}
