package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;

public class ProvenanceContradiction extends ProvenanceTree {   
    final Map<ExprHasName, Object> bindings;
    Expr rel;
    Expr tupleExpr;
    ExprUnary lastNOOP;

    public ProvenanceContradiction(Expr rel, Expr tupleExpr, ExprUnary lastNOOP, Map<ExprHasName, Object> provBindings) {
        // Create a new map since the provBindings passed may be reused/modified by caller
        this.bindings = new HashMap<ExprHasName, Object>(provBindings);
        this.rel = rel;
        this.tupleExpr = tupleExpr;
        this.lastNOOP = lastNOOP;
    }

    @Override
    public ProvenanceTree clone() {
        return new ProvenanceContradiction(rel, tupleExpr, lastNOOP, new HashMap<ExprHasName, Object>(bindings)).annotateAll(this.getAnnotations());
    }
    
    @Override
    public ProvenanceTree simplify() {
        return this;
    }
    
    @Override
    public Set<ProvenanceTree> orsplit() {
        Set<ProvenanceTree> trees = new HashSet<ProvenanceTree>();
        trees.add(this.clone());
        return trees;
    }
    
    @Override
    public ProvenanceTrace trace() {    
        // BAD SOLUTION: If there is a NOOP wrapping this field reference, use that NOOP's posn instead.
        // Bad because span() will still explore the field's pos. Instead, just use the NOOP-wrapped field.    
        Expr e;
        if(lastNOOP != null && lastNOOP.sub.equals(rel)) {
            e = tupleExpr.in(lastNOOP);
        } else {
            e = tupleExpr.in(rel);
        }                   
        //System.err.println("contradiction e.pos: "+e.pos);
        return new ProvenanceTrace(e, true, new ArrayList<ProvenanceLeaf>(), bindings, new ArrayList<ProvenanceTrace>(), getAnnotations());
    }
    
    @Override
    public ProvenanceTree expandAntecedents(Module root, A4Solution orig, A4Solution model) {
        return this;
    }
    
    /*@Override
    public Set<Provenance> allExplains() {
        // Don't return empty; need a single element for cross-product in caller        
        List<Expr> single = new ArrayList<Expr>(1);
        single.add(ExprConstant.TRUE);
        Set<Provenance> result = new HashSet<Provenance>(1);
        result.add(new Provenance(single, this.bindings));
        return result;
    }

    @Override
    public Graph buildDisplay(Graph context) {
        if(context == null) {
            context = new SingleGraph("First explanation");
            context.addAttribute("ui.stylesheet", graphStyleSheet);
        }

        Node n;
        if(context.getNode("X") == null) 
            n = context.addNode("X");
        else
            n = context.getNode("X");

        n.addAttribute("ui.label", "X");
        n.addAttribute("ui.color", 0.0);

        return context;
    }
*/
    @Override
    public String toString() {
        if(this.bindings.size() == 0)
            return "<CONTRADICTION: "+rel+"("+tupleExpr+")>";
        else return "<CONTRADICTION: "+rel+"("+tupleExpr+") via: "+this.bindings+">";

    }

    @Override
    public ProvenanceTree disallowCollapse() {        
        return this; // do nothing
    }
}
