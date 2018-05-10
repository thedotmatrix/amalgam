package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.List;
import java.util.Map;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;

public class Provenance {
    public List<Expr> alphas;
    public Map<ExprHasName, Object> bindings;
    
    public Provenance(List<Expr> alphas, Map<ExprHasName, Object> bindings) {
        this.alphas = alphas;
        this.bindings = bindings;
    }
    
}
