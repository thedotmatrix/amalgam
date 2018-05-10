package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.HashSet;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.WrappedExpr;

public class ProvenanceLeaf extends ProvenanceTree implements ExprContainer {
    Expr contents;
    WrappedExpr skeleton;

    public ProvenanceLeaf(Expr contents) {
        // limited simplification
        this.contents = AmalgamVisitorHelper.eliminateDoubleNegation(contents);
        this.skeleton = null;
    }

    @Override
    public ProvenanceTree clone() {
        return new ProvenanceLeaf(contents).annotateAll(getAnnotations());
    }

    @Override
    public ProvenanceTree simplify() {
        return this;
        // simplify method won't be called anymore; don't rely on this
    }

    @Override
    public Set<ProvenanceTree> orsplit() {
        Set<ProvenanceTree> trees = new HashSet<ProvenanceTree>();
        trees.add(this.clone());
        return trees;
    }

    @Override
    public ProvenanceTrace trace() throws Err {
        throw new ErrorFatal("Should never trace down to an alpha leaf, only failures");
    }

    //@Override
    public ProvenanceTree expandAntecedents(Module root, A4Solution orig, A4Solution model) throws Err {
        // Is this a non-ground fmla? Then this is an unexpanded antecedent
        // We want to know which ground literals in the instance make this fmla true.
        //System.err.println("Calling Ground Visitor to explain: "+contents+" ... ");
        ProvenanceTree result = new AmalgamGroundVisitor(root, orig, model, contents).visitThis(contents).annotateAll(this.getAnnotations());
        //System.err.println("DONE calling Ground Visitor to explain: "+contents);
        //System.err.println("Produced Tree: "+result);
        return result;
    }

  /*  @Override
    public Set<Provenance> allExplains() {
        Set<Provenance> result = new HashSet<Provenance>();
        List<Expr> single = new ArrayList<Expr>(1);
        single.add(contents);
        result.add(new Provenance(single, new HashMap<ExprHasName, Object>()));
        return result;
    }

    @Override
    public ProvenanceTree expandAntecedents(Module root, A4Solution orig, A4Solution model) throws Err {
        // Is this a non-ground fmla? Then this is an unexpanded antecedent
        // We want to know which ground literals in the instance make this fmla true.
        //System.err.println("Calling Ground Visitor to explain: "+contents+" ... ");
        ProvenanceTree result = new AmalgamGroundVisitor(root, orig, model, contents).visitThis(contents);
        //System.err.println("DONE calling Ground Visitor to explain: "+contents);
        //System.err.println("Produced Tree: "+result);
        return result;
    }


    @Override
    public Graph buildDisplay(Graph context) {
        if(context == null) {
            context = new SingleGraph("First explanation");
            context.addAttribute("ui.stylesheet", graphStyleSheet);
        }

        Node n;
        if(context.getNode(contents.toString()) == null)
            n = context.addNode(contents.toString());
        else
            n = context.getNode(contents.toString());
        n.addAttribute("ui.label", contents.toString());
        n.addAttribute("ui.color", 0.0);

        return context;
    }
*/
    @Override
    public String toString() {
        return "<"+contents+">";
    }

    @Override
    public ProvenanceTree disallowCollapse() {
        return this; // do nothing
    }

    public Expr getContents() {
        return contents;
    }
}
