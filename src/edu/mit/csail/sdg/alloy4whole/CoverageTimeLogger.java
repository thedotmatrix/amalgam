package edu.mit.csail.sdg.alloy4whole;

import java.util.Stack;

public class CoverageTimeLogger {    
    Stack<Long> timeList = new Stack<>(); 
    
    public void pushTime() {
        timeList.push(System.currentTimeMillis());
    }
    
    public void popTime(String s) {
        System.out.println("Time " + s + ": " + ((System.currentTimeMillis() - timeList.pop()) / 1000) + " s");
    }
}
