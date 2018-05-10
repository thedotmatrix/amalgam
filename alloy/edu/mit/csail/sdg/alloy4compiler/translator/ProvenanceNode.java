package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;

public class ProvenanceNode extends ProvenanceTree {
    static public enum Op {PAND, POR};
    List<ProvenanceTree> contents;
    Expr cause;
    boolean sign;
    Op op;
    
    /**
     * If true, this node can be simplified out for having only one child.
     * If false, this node will always exist
     */
    boolean allowCollapse = true;    

    public static ProvenanceNode construct(Op op, Expr cause, boolean sign, List<ProvenanceTree> contents) throws Err {
        if(contents.size() < 1) {
            throw new ErrorFatal("ProvenanceNode created with no contents; some formula has not been properly explored. Cause="+cause);
        }
        return new ProvenanceNode(op, cause, sign, contents);
    }
    private ProvenanceNode(Op op, Expr cause, boolean sign, List<ProvenanceTree> contents) {
        this.contents = contents;
        this.cause = cause; 
        this.sign = sign;
        this.op = op;
        // null represents "this condition is unchanged"
        while(this.contents.contains(null)) this.contents.remove(null);
    }  

    public ProvenanceNode disallowCollapse() {
        allowCollapse = false;
        return this;
    }
    
    @Override
    public ProvenanceTree simplify() throws Err {
        return this;
    }
    /*
    @Override
    public ProvenanceTree simplify() throws Err {
        // Recursively simplify the tree
        List<ProvenanceTree> simplifiedContents = new ArrayList<ProvenanceTree>();
        for(ProvenanceTree sub : contents) {       
            ProvenanceTree newsub = sub.simplify();

            // PREVIOUSLY simplification merged pand nodes of the same sign. This was OK for gathering sets
            // of alphas but bad when printing trees, because it caused unrelated alphas to be grouped together.             
            simplifiedContents.add(newsub);
           
        }
        // TODO: can't remove duplicates here, either via equals or to-string comparison, because
        // the tree structure may differ. Could use a smarter comparison that checks equivalence.
        // For now, remove duplicates _after_.
        
        ProvenanceTree result;
        // Dont have a PAND or POR node if there's only one child
        // Carry over annotations regardless
        if(simplifiedContents.size() == 1 && this.allowCollapse) {         
            result = simplifiedContents.get(0);
            // lower-level annotations go earlier in the list. we're using .add() so need to reverse order of addition
            List<Annotation> revAs = this.getAnnotations();
            Collections.reverse(revAs);
            for(Annotation a : revAs) {
                result.annotateFirst(a);
            }            
        } else {
            result = new ProvenanceNode(op, cause, sign, simplifiedContents);
            for(Annotation a : this.getAnnotations()) {
                result.annotate(a);
            }                        
        }
        return result;
    }*/

    @Override
    public ProvenanceTree clone() {
        List<ProvenanceTree> clonedContents = new ArrayList<ProvenanceTree>();
        for(ProvenanceTree content : this.contents) {
            clonedContents.add(content.clone());
        }
        return new ProvenanceNode(op, cause, sign, clonedContents).annotateAll(this.getAnnotations());
    }

    @Override
    public Set<ProvenanceTree> orsplit() {        
        Set<ProvenanceTree> splitTrees = new HashSet<ProvenanceTree>();
        switch(this.op) {
        case PAND: {
            // annotate this first new tree in accumulator
            splitTrees.add(new ProvenanceNode(Op.PAND, cause, sign, new ArrayList<ProvenanceTree>()).annotateAll(this.getAnnotations()));
            
            for(ProvenanceTree content : this.contents) {
                Set<ProvenanceTree> crossTrees = new HashSet<ProvenanceTree>();
                // Cross product split contents
                // For everything in contents (i.e., everything to be folded over)
                for(ProvenanceTree splitContent : content.orsplit()) {
                    //System.err.println("PAND: splitContent had annotations: "+splitContent.getAnnotations());
                    // For everything in accumulator set
                    for(ProvenanceTree splitTree : splitTrees) {
                        ProvenanceTree crossTree = splitTree.clone();           // clone this element of accumulator
                        ((ProvenanceNode)crossTree).contents.add(splitContent); // add recursively split content from to-fold                           
                        crossTrees.add(crossTree);                              // add to results of this iteration
                    }
                }
                splitTrees.clear();
                splitTrees.addAll(crossTrees);
            }            
            break;
        }
        case POR: {
            // Convert OR(a,b,...) into split(a) union split(b), ...
            for(ProvenanceTree content : this.contents) { 
                // Recursively split each tree inside this one
                //System.err.println("POR content had child with annotations: "+content.getAnnotations());
                // This needs to inherit the annotations of its parent. annotate before calling orsplit
                splitTrees.addAll(content.clone().annotateFirstReverse(this.getAnnotations()).orsplit());
            }
            break;
        }
        }               
        return splitTrees;
    }
    
    @Override
    public ProvenanceTrace trace() throws Err {
        List<ProvenanceLeaf> alphas = new ArrayList<ProvenanceLeaf>();
        List<ProvenanceTrace> consequences = new ArrayList<ProvenanceTrace>();
        for(ProvenanceTree content : contents) {
            if(content instanceof ProvenanceLeaf) alphas.add((ProvenanceLeaf)content);
            else consequences.add(content.trace());
        }
        return new ProvenanceTrace(cause, sign, alphas, new HashMap<ExprHasName, Object>(), consequences, getAnnotations());
    }

    @Override
    public ProvenanceTree expandAntecedents(Module root, A4Solution orig, A4Solution model) throws Err {
        // Expand children
        List<ProvenanceTree> newChildren = new ArrayList<ProvenanceTree>();
        for(ProvenanceTree sub : contents) {            
            newChildren.add(sub.expandAntecedents(root,orig,model));
        }
        return new ProvenanceNode(op, cause, sign, newChildren).annotateAll(this.getAnnotations()); 
    }
    
  /*  @Override
    public Set<Provenance> allExplains() throws Err {
        Set<Provenance> result = new HashSet<Provenance>();
        if(op.equals(Op.PAND)) {
            for(ProvenanceTree child : contents) {
                // cross product. Example:
                // Suppose this node has 2 children: {{a,b,c}, {d,e}} and {{f,g},{h}}. 
                // We need both children to be met, and each has 2 options. So:
                // {a,b,c,f,g},{a,b,c,h}, {d,e,f,g}, {d,e,h}.
                if(result.size() == 0)
                    result.addAll(child.allExplains()); // base case for the product
                else {
                    Set<Provenance> newresult = new HashSet<Provenance>();
                    for(Provenance aProvenanceSoFar : result) {
                        List<Expr> sofar = aProvenanceSoFar.alphas;
                        for(Provenance extendwith : child.allExplains()) {
                            List<Expr> combined = new ArrayList<Expr>(sofar);
                            combined.addAll(extendwith.alphas);
                            Provenance newprov = new Provenance(combined, aProvenanceSoFar.bindings);
                            newprov.bindings.putAll(extendwith.bindings);
                            newresult.add(newprov);
                        }
                    }                    
                    result = newresult;
                }                                
            }
        } else { // POR
            for(ProvenanceTree child : contents) {
                // this child's explanation
                result.addAll(child.allExplains());
            }
            // TODO Note that we may accumulate duplicates here since Expr uses Object.equals
        }            

        return result;
    }*/



   /* @Override
    public Graph buildDisplay(Graph context) {
        if(context == null) {
            context = new SingleGraph("First explanation");
            context.addAttribute("ui.stylesheet", graphStyleSheet);
        }

        Node n;
        if(context.getNode(cause.toString()) == null) 
            n = context.addNode(cause.toString());
        else
            n = context.getNode(cause.toString());

        n.addAttribute("ui.label", cause.toString());
        n.addAttribute("ui.color", 1.0);

        for(ProvenanceTree subTree : contents) {
            subTree.buildDisplay(context);
            String edgeId = cause.toString()+"__"+subTree.toString();
            Edge e;
            if(context.getEdge(edgeId) == null)
                e = context.addEdge(edgeId, cause.toString(), subTree.toString(), true);            
        }

        return context;
    }*/

    @Override
    public String toString() {
        return this.toString("");
    }
    String toString(String indent) {
        final String vSpace="\n\n";
        final String hSpace="    ";
        StringBuilder result = new StringBuilder();
        result.append(indent+"*"+cause+"*"+vSpace);
        for(ProvenanceTree content : contents) {
            result.append(content.toString(indent+hSpace)+vSpace);
        }
        return result.toString();
    }
}
