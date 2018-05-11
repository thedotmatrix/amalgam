package edu.mit.csail.sdg.alloy4compiler.translator;

// Give access to the static menu item that this class needs
import static edu.mit.csail.sdg.alloy4.A4Preferences.ProvStyle;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4compiler.ast.Browsable;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTree.Annotation;
import edu.mit.csail.sdg.alloy4whole.SwingLogPanel;



public class ProvenanceTrace {
    final Expr failure;
    /** As in Diff eval visitor, sign = sign in ORIGINAL model. So "becomes false" = true 
     *  This is NOT the same as whether the query was "why" or "why not". */
    final boolean sign;
    final Map<ExprHasName, Object> bindings;
    final List<ProvenanceLeaf> alphas;
    final List<ProvenanceTrace> consequences;
    final int maxdepth;    
    final int numAlphas;
    final List<ProvenanceTree.Annotation> annotations;

    public ProvenanceTrace(Expr failure, boolean sign, List<ProvenanceLeaf> alphas, Map<ExprHasName, Object> bindings, 
            List<ProvenanceTrace> consequences, List<ProvenanceTree.Annotation>annotations) {
        this.failure = failure;
        this.sign = sign;
        this.alphas = alphas;
        this.bindings = bindings;
        this.consequences = consequences;
        this.maxdepth = maxDepth();  
        this.numAlphas = uniqueAlphas().size();
        this.annotations = annotations;        
    }
    public Set<String> uniqueAlphas() {
        Set<String> unqs = new HashSet<String>();
        for(ProvenanceLeaf alpha : alphas) {
            unqs.add(alpha.contents.toString());
        }
        for(ProvenanceTrace conseq : this.consequences) {
            unqs.addAll(conseq.uniqueAlphas());
        }
        return unqs;
    }
    public List<ProvenanceLeaf> getAlphas() {
        List<ProvenanceLeaf> result = new ArrayList<ProvenanceLeaf>(alphas);
        for(ProvenanceTrace consequence : consequences) {
            result.addAll(consequence.getAlphas());
        }
        return result;
    }
    public int maxDepth() {
        int currentMax = 0;
        for(ProvenanceTrace consequence : consequences) {
            int submax = consequence.maxDepth();
            if(submax > currentMax) currentMax = submax;
        }
        return currentMax+1;
    }
    public int maxHighlight() {
        int maxArea = 0;
        //String log = "";
        for(Browsable failure : this.allFailures().values()) {
            Pos p = failure.span();
            int area = Math.abs(p.x-p.x2) * Math.abs(p.y-p.y2);
            //log += failure+"["+area+"],";
            if(area > maxArea) maxArea = area;
        }
        for(List<ProvenanceLeaf> alphas : this.allAlphas().values()) {
            for(ProvenanceLeaf alpha : alphas) {
                Pos p = alpha.contents.pos();
                int area = (Math.abs(p.x-p.x2)+1) * (Math.abs(p.y-p.y2)+1);
                //log += alpha+"["+area+"],";
                if(area > maxArea) maxArea = area;
            }
        }
        return maxArea;
    }

    // Printers
    @Override
    public String toString() {
        return this.toString("");
    }
    // To the evaluator or elsewhere (no "log" element)
    public String toString(String tup, String rel) {
        StringBuilder result = new StringBuilder();
        result.append((sign ? "+" : "-")+tup+" in "+rel+"\n\n");
        result.append(this.toString(""));        
        result.append("\nAlphas:\n");
        result.append(getAlphas());
        return result.toString();
    }
    private static String effectString(boolean sign) {
        return sign ? "" : "NOT ";
    }
    private String toString(String indent) {
        StringBuilder result = new StringBuilder();
        // failure / success        
        result.append(indent+effectString(this.sign)+failure+" "+this.annotations+"\n");

        // bindings
        if(!bindings.isEmpty()) result.append("\n"+indent+"...when we plug in: "+bindings);
        // alphas
        //if(alphas.size() + consequences.size() > 0) result.append(indent+"because:\n");
        if(alphas.size() > 0) result.append(indent+"  combined with:\n");
        for(ProvenanceLeaf alpha : alphas) {
            result.append(indent+"   "+alpha.contents+" "+alpha.getAnnotations()+"\n");
        }
        // consequences
        if(!consequences.isEmpty()) result.append(indent+"leads to:\n");
        for(ProvenanceTrace consequence : consequences) {
            result.append(consequence.toString(indent+"    "));
        }                        
        return result.toString();
    }
    
    public void toString(boolean why, String tup, String rel, SwingLogPanel log) {
        log.log("\n");
        log.logDivider();
        log.logBold("Explaining "+(why ? "why" : "why not")+": ");
        // all alphas link
        Set<Prov> provs = new HashSet<Prov>();
        for(Entry<Integer, List<ProvenanceLeaf>> alphas : allAlphas().entrySet()) {
            for(ProvenanceLeaf alpha : alphas.getValue()) {
                provs.add(new Prov(alphas.getKey(), alpha.contents.pos(), Prov.NodeType.NEUTRAL));
            }
        }
        log.provLink(tup, "", maxdepth, provs);
        log.logBold(" in");
        // all exprs link
        provs = new HashSet<Prov>();
        for(Entry<Integer, Browsable> failure : allFailures().entrySet()) {
            provs.add(new Prov(failure.getKey(), failure.getValue().span(), Prov.NodeType.NEUTRAL));
        }
        log.provLink(rel, "", maxdepth, provs);
        log.log("\n");        
        if(ProvStyle.get() == 1) {
            List<ProvenanceTrace> traces = new ArrayList<ProvenanceTrace>();
            traces.add(this);
            simpleTrace(traces,log,1);
        }
        else {
            log.logBold("The top-level constraint:\n");
            expertTrace(log,0);
        }
        log.logDivider();        
        log.log("\n");        
    }
    private void expertTrace(SwingLogPanel log, int depth) {
        // failure / success
        Set<Prov> provs = new HashSet<Prov>();
        log.logBold(indent(depth)+effectString(this.sign));            
        provs.add(new Prov(depth, failure.span(), (this.sign ? Prov.NodeType.BECOMES_FALSE : Prov.NodeType.BECOMES_TRUE)));
        log.provLink(trim(failure.toString(), depth), "", maxdepth, provs);
        log.log("\n");   
        // bindings
        if(!bindings.isEmpty()) {
            log.logBold(indent(depth)+"...when we plug in: ");
            log.log(bindings.toString());
            log.log("\n");
        }
        // alphas        
        if(alphas.size() > 0) log.logBold(indent(depth)+"combined with:\n");
        for(ProvenanceLeaf alpha : alphas) {
            log.log(indent(depth));
            provs = new HashSet<Prov>();
            provs.add(new Prov(depth, alpha.contents.span(), Prov.NodeType.ALPHA));
            // Show only a subset of annotations in log
            Collection<Annotation> anns = Annotation.forLogOnly(ProvStyle.get(),alpha.getAnnotations());   
            // link for alpha
            log.provLink(trim(alpha.contents.toString(), depth), anns.toString(), maxdepth, provs);
            log.log("\n");
        }
        // consequences  
        for(ProvenanceTrace consequence : consequences) {
            if(consequence.annotations.size() > 0) log.logBold(indent(depth)+"leads to (via: "+Annotation.forLogOnly(ProvStyle.get(),consequence.annotations)+"):\n");
            else log.logBold(indent(depth)+"leads to:\n");
            consequence.expertTrace(log, depth+1);
        }
    }
    private static void simpleTrace(List<ProvenanceTrace> traces, SwingLogPanel log, int depth) {
        // REASONS
        // start
        if(depth==1) {
            log.logBold("Starting with the top-level constraint...\n");
            for(int i=0; i<traces.size(); i++) {
                ProvenanceTrace t = traces.get(i);
                simpleReason(false,t,log,depth,i);
                if(i<traces.size()-1) log.log(" ");
            }
        }
        // intermediate (variable verbosity)
        else if(!traces.get(0).consequences.isEmpty()) {
            log.logBold("which leads to... ");
            for(int i=0; i<traces.size(); i++) {
                ProvenanceTrace t = traces.get(i);
                simpleReason(true,t,log,depth,i);
                if(i<traces.size()-1) log.log(" ");
            }
        }
        // end  
        else {
            log.logBold("that leads to literals...\n");
            for(int i=0; i<traces.size(); i++) {
                ProvenanceTrace t = traces.get(i);
                simpleReason(false,t,log,depth,i);
                if(i<traces.size()-1) log.log("\n");
            }
        }
        log.log("\n");
        // DEDUCTIONS
        if(!traces.get(0).consequences.isEmpty()) log.logBold(indent(1)+"then:\n");
        List<String> alphas = new ArrayList<String>();
        for(ProvenanceTrace t : traces) for(ProvenanceLeaf a : t.alphas) alphas.add(a.contents.toString());
        for(int i=0; i<traces.size(); i++) {
            ProvenanceTrace t = traces.get(i);
            // consequential annotations
            for(ProvenanceTrace consequence : t.consequences) {
                simpleAnnotations(log, consequence.annotations);
            }
            // alphas
            for(ProvenanceLeaf a : t.alphas) {
                simpleAlpha(t, a, log, depth);
            }
            if(depth!=1 && (!t.alphas.isEmpty() || !t.consequences.isEmpty())) log.logBold(indent(1)+"for "+simpleTag(depth,i)+",\n");
        }
        // BFS RECURSION
        List<ProvenanceTrace> rec = new ArrayList<ProvenanceTrace>();
        for(ProvenanceTrace trace : traces) {
            rec.addAll(trace.consequences);
        }
        if(!rec.isEmpty()) simpleTrace(rec,log,depth+1);
    }
    private static void simpleReason(boolean simple, ProvenanceTrace t, SwingLogPanel log, int depth, int i) {
        Set<Prov> provs = new HashSet<Prov>();
        log.logBold(effectString(t.sign));            
        Prov prov = new Prov(depth, t.failure.span(), (t.sign ? Prov.NodeType.BECOMES_FALSE : Prov.NodeType.BECOMES_TRUE));
        provs.add(prov);
        String link = simple ? simpleTag(depth,i) : t.failure.toString();
        if(!t.bindings.isEmpty()) link += ", when we plug in "+t.bindings.toString();
        log.provLink(link, "", t.maxdepth, provs);
    }
    private static void simpleAlpha(ProvenanceTrace t, ProvenanceLeaf alpha, SwingLogPanel log, int depth) {
        log.log(indent(1));
        Set<Prov> provs = new HashSet<Prov>();
        provs.add(new Prov(depth, alpha.contents.span(), Prov.NodeType.ALPHA));
        // Show only a subset of annotations in log
        Collection<Annotation> anns = Annotation.forLogOnly(ProvStyle.get(), alpha.getAnnotations());   
        // link for alpha
        log.provLink(trim(alpha.contents.toString(),0), anns.toString(), t.maxdepth, provs);
        log.log("\n");
    }
    private static void simpleAnnotations(SwingLogPanel log, List<Annotation> annotations) {
        for(Annotation a : Annotation.forLogOnly(ProvStyle.get(), annotations)) {
            log.log(indent(1));
            log.annoLink(a.toString());
            log.log("\n");
        }
    }
    private static String simpleTag(int depth, int i) {
        return "["+depth+"-"+(i+1)+"]";
    }

    // Helpers
    private static String trim(String link, int depth) {
        // trim link        
        int permissibleLength = overflow-indent(depth).length();
        if(link.length() > permissibleLength) {
            link = link.substring(0, permissibleLength)+"...";
        }
        return link;
    }
    private final static int overflow = 80;
    private static String indent(int depth) {
        String indent = "";
        for(int i=0;i<depth;i++) {
            // tabs are too large for even modestly deep trees
            indent = indent + "  ";
        }
        return indent;
    }
    private Map<Integer, List<ProvenanceLeaf>> allAlphas() { return allAlphas(0); }
    private Map<Integer, List<ProvenanceLeaf>> allAlphas(int depth) {
        Map<Integer, List<ProvenanceLeaf>> alphas = new HashMap<Integer, List<ProvenanceLeaf>>();
        alphas.put(depth, this.alphas);
        for(ProvenanceTrace trace : this.consequences) {
            alphas.putAll(trace.allAlphas(depth+1));
        }
        return alphas;
    }
    private Map<Integer, Browsable> allFailures() { return allFailures(0); }
    private Map<Integer, Browsable> allFailures(int depth) {
        Map<Integer, Browsable> failures = new HashMap<Integer, Browsable>();
        failures.put(depth, this.failure);
        for(ProvenanceTrace trace : this.consequences) {
            failures.putAll(trace.allFailures(depth+1));
        }
        return failures;
    }
    
    public Set<Expr> getLeafFailures() {
        Set<Expr> result = new HashSet<>(1);
        if (consequences.isEmpty()) {
            result.add(failure);
            return result;
        }
        for(ProvenanceTrace consequence : consequences) {
            result.addAll(consequence.getLeafFailures());
        }
        return result;
    }
}
