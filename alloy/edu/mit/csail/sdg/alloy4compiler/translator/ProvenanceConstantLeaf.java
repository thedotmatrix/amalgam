package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;

/**
 * Represents a true or false that have come about because of bounds (rather than an actual constant in the theory) 
 * @author tn
 */
public class ProvenanceConstantLeaf extends ProvenanceLeaf {
    static public enum TYPE {
        TRUE_WRT_BOUNDS,      // empty conjunction
        FALSE_WRT_BOUNDS      // empty disjunction
        };
    Expr expr;                // the expression that had an empty upper bound and led to this true/false
    TYPE type;

    public ProvenanceConstantLeaf(TYPE type, Expr expr) {
        // A ConstantLeaf is a Leaf.
        super(type == TYPE.TRUE_WRT_BOUNDS ? ExprConstant.TRUE : ExprConstant.FALSE);
        this.expr = expr;
        this.type = type;
    }
    
    @Override
    public ProvenanceTree clone() {
        return new ProvenanceConstantLeaf(type, expr).annotateAll(this.getAnnotations());
    }
    
    @Override
    public ProvenanceTree expandAntecedents(Module root, A4Solution orig, A4Solution model) {
        return this;
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
        List<ProvenanceTrace> consequences = new ArrayList<ProvenanceTrace>();
        List<ProvenanceLeaf> bounds = new ArrayList<ProvenanceLeaf>();
        switch(this.type) {
        case TRUE_WRT_BOUNDS: {
            consequences.add(new ProvenanceTrace(ExprConstant.TRUE, true, new ArrayList<ProvenanceLeaf>(), new HashMap<ExprHasName, Object>(), new ArrayList<ProvenanceTrace>(), getAnnotations()));
            bounds.add(this);
            break;
        }
        case FALSE_WRT_BOUNDS: {
            consequences.add(new ProvenanceTrace(ExprConstant.FALSE, true, new ArrayList<ProvenanceLeaf>(), new HashMap<ExprHasName, Object>(), new ArrayList<ProvenanceTrace>(), getAnnotations()));
            bounds.add(this);
            break;
        }
        }
        return new ProvenanceTrace(expr, true, bounds, new HashMap<ExprHasName, Object>(), consequences, getAnnotations());
    }

 /*   @Override
    public Set<Provenance> allExplains() {
        // TODO: want to give more context in literal provenance than just "true" or "false"
        Set<Provenance> result = new HashSet<Provenance>();
        List<Expr> single = new ArrayList<Expr>(1);
        if(type.equals(TYPE.TRUE_WRT_BOUNDS)) single.add(ExprConstant.TRUE);
        else if(type.equals(TYPE.FALSE_WRT_BOUNDS)) single.add(ExprConstant.FALSE);
        result.add(new Provenance(single, new HashMap<ExprHasName, Object>()));
        return result;
    }

    public ProvenanceTree expandAntecedents(Module root, A4Solution orig, A4Solution model) throws Err {
        return this;
    }

    @Override
    public Graph buildDisplay(Graph context) {          
        if(context == null) {            
            context = new SingleGraph("First explanation");
            context.addAttribute("ui.stylesheet", graphStyleSheet);
        }

        Node n;
        if(context.getNode(type.toString()) == null) 
            n = context.addNode(type.toString());
        else
            n = context.getNode(type.toString());
        n.addAttribute("ui.label", type.toString());
        n.addAttribute("ui.color", 0.0);

        return context;
    }
*/
    @Override
    public String toString() {
        return "<"+type+">";
    }

    @Override
    public ProvenanceTree disallowCollapse() {
        return this; // do nothing
    } 
}
