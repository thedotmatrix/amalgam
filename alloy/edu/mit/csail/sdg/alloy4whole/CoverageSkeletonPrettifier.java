package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTraceWrapper;

public class CoverageSkeletonPrettifier {
    static int count(String s, String c) {
        return s.length() - s.replace(c, "").length();
    }
    
    static String prettify(ProvenanceTraceWrapper s) {
        String[] lst = s.toString().split("\n");
        StringBuffer sb = new StringBuffer();
        
        int indentLevel = 0;
        for (int i = 0; i < lst.length; i++) {
            for (int t = 0; t < indentLevel; t++) {
                sb.append("  ");
            }
            sb.append(lst[i]);
            sb.append("\n");
            indentLevel += count(lst[i], "(") - count(lst[i], ")");
        }
        return sb.toString(); 
    }
}
