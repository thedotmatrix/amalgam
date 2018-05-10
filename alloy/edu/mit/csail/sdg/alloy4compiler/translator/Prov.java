package edu.mit.csail.sdg.alloy4compiler.translator;

import edu.mit.csail.sdg.alloy4.Pos;

public class Prov {
    public final int d;
    public final Pos p;
    public final NodeType t;        
    public Prov(int d, Pos p, NodeType t) {
        this.d = d;
        this.p = p;
        this.t = t;
    }
    public static enum NodeType {BECOMES_FALSE, BECOMES_TRUE, ALPHA, NEUTRAL};
}
