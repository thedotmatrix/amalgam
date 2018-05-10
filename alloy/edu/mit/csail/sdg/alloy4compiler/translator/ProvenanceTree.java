package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;

public abstract class ProvenanceTree { 
    @Override
    public abstract ProvenanceTree clone();
    public abstract ProvenanceTree simplify() throws Err;
    public abstract Set<ProvenanceTree> orsplit();
    public abstract ProvenanceTrace trace() throws Err;
    
    static final String graphStyleSheet = ""
            + "node {"
            + "       fill-mode: dyn-plain;"
            + "       size-mode: dyn-size;"
            + "       fill-color: red, green;"
            + "}"
            + "";

    Object toString(String tabs) {
        return tabs+this.toString();
    }
        
    abstract public ProvenanceTree disallowCollapse();

    abstract public ProvenanceTree expandAntecedents(Module root, A4Solution orig, A4Solution model) throws Err;
    
    /**
     * Record extra information as needed in each ProvenanceTree object.
     * For instance, might remember that a given collected alpha is a failed existential binding. 
     * Can also record desugaring reasons, and since this list is *ordered*, 
     * a node should have a record of the desugarings it passed through
     */
    private final List<Annotation> annotations = new LinkedList<Annotation>();
    public ProvenanceTree annotate(Annotation annotation) {              
        this.annotations.add(annotation);        
        return this;
    }
    public ProvenanceTree annotateFirst(Annotation annotation) {      
        this.annotations.add(0,annotation); // add at beginning of list        
        return this;
    }
    public ProvenanceTree annotateFirstReverse(List<Annotation> newAnnotations)
    {
        if(newAnnotations.size() < 1) return this; // for debugging, don't display an empty annotateAll
        Collections.reverse(newAnnotations);
        for(Annotation a: newAnnotations) {
            this.annotateFirst(a);
        }
        return this;
    }
    public ProvenanceTree annotateAll(List<Annotation> annotations) {   
        if(annotations.size() < 1) return this; // for debugging, don't display an empty annotateAll
        // TN note: useful lesson for teaching here: I actually fell for the "forgot this." mistake.
        this.annotations.addAll(annotations);         
        return this;
    }
    public List<Annotation> getAnnotations() {
        return new LinkedList<Annotation>(annotations); // defensive copy
    }          
    
    // Can't use enum because parameters differ
    static abstract class Annotation {
        abstract public boolean showInLog(int level); 
        
        static public Collection<Annotation> forLogOnly(int level, Collection<Annotation> as) {
            List<Annotation> copy = new LinkedList<Annotation>(as);
            Iterator<Annotation> ai = copy.iterator();
            while(ai.hasNext()) {
                Annotation a = ai.next();
                if(!a.showInLog(level)) ai.remove(); // remove last next()
            }
            return copy;
        }
    }
    static class PAUnavailableOr extends Annotation {
        @Override public String toString() {
            return "eliminate OR branch";
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    }
    static class PAFollowAND extends Annotation {
        @Override public String toString() {
            return "descend into AND";
        }
        @Override public boolean showInLog(int level) { return level>=3;}
    }
    static class PAExpandUNIV extends Annotation {
        @Override public String toString() {
            return "expand UNIV";
        }
        @Override public boolean showInLog(int level) { return level>=1;}
    }
    static class PAExpandIDEN extends Annotation {
        @Override public String toString() {
            return "IDEN defined on existing atoms";
        }
        @Override public boolean showInLog(int level) { return level>=1; }
    }        
    static class PAUnavailableExist extends Annotation {
        ExprHasName var;
        Object atom;
        PAUnavailableExist(ExprHasName var, Object atom) {
            this.var = var;
            this.atom = atom;
        }        
        @Override public String toString() {
            return "eliminate "+var+"="+atom;
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    }
    static class PABindForall extends Annotation {
        ExprHasName var;
        Object atom;
        PABindForall(ExprHasName var, Object atom) {
            this.var = var;
            this.atom = atom;
        }        
        @Override public String toString() {
            return "let "+var+"="+atom;
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    }
    static class PATryOr extends Annotation {
        @Override public String toString() {
            return "explore OR branch";
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    }
    static class PATryExist extends Annotation {
        ExprHasName var;
        Object atom;
        PATryExist(ExprHasName var, Object atom) {
            this.var = var;
            this.atom = atom;
        }
        @Override public String toString() {
            return "explore "+var+"="+atom;
        }        
        @Override public boolean showInLog(int level) { return level>=2; }
    }
    static class PADesugarQuantifier extends Annotation {
        ExprHasName var;        
        PADesugarQuantifier(ExprHasName var) {
            this.var = var;            
        }
        @Override public String toString() {
            return "desugar quantifier "+var;
        }        
        @Override public boolean showInLog(int level) { return level>=2; }
    }
    static class PADesugarUnary extends Annotation {
        ExprUnary.Op op;        
        PADesugarUnary(ExprUnary.Op op) {
            this.op = op;            
        }
        @Override public String toString() {
            return "desugar "+op;
        }      
        @Override public boolean showInLog(int level) { return level>=2; }
    }
    static class PAAtomicIN extends Annotation {
        @Override public String toString() {
            return "desugar atomic in";
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    }
    static class PADesugarBinary extends Annotation {
        ExprBinary.Op op;        
        PADesugarBinary(ExprBinary.Op op) {
            this.op = op;            
        }
        @Override public String toString() {
            return "desugar "+op;
        }        
        @Override public boolean showInLog(int level) { return level>=2; }
    } 
    static class PADesugarITE extends Annotation {
        @Override public String toString() {
            return "desugar if-then-else";
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    }  
    static class PADesugarLet extends Annotation {
        @Override public String toString() {
            return "desugar let";
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    } 
    static class PAResolveCall extends Annotation {
        @Override public String toString() {
            return "resolve pred call";
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    } 
    static class PADesugarORContext extends Annotation {
        @Override public String toString() {
            return "desugar OR";
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    }
    static class PADesugarANDContext extends Annotation {
        @Override public String toString() {
            return "desugar AND";
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    } 
    static class PADesugarMultiplicityInIN extends Annotation {
        @Override public String toString() {
            return "desugar IN multiplicity";
        }
        // this one is for, e.g., "f: Node -> one Node"
        @Override public boolean showInLog(int level) { return level>=2; }
    } 
    static class PADesugarComprehension extends Annotation {
        @Override public String toString() {
            return "desugar comprehension";
        }
        @Override public boolean showInLog(int level) { return level>=2; }
    } 
    static class PAFixedEquality extends Annotation {
        boolean diffLeft;
        boolean diffRight;
        PAFixedEquality(boolean diffLeft, boolean diffRight) {
            this.diffLeft = diffLeft;
            this.diffRight = diffRight;
        }
        @Override public String toString() {
            return "fixed equality";
        }
        @Override public boolean showInLog(int level) { return level>=3; }
    }    
}
