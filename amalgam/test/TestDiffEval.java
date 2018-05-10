package test;
//package amalgam.test.unit;

/*
 * Need to add JUnit 4 package to Project build path 
 * Need to make sure this file is in a "source" folder for Eclipse (build path -> use as source folder)
 * 
 */

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertFalse;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public class TestDiffEval {    
    
    @Test
    public final void test() {
        assertTrue(true);
        assertFalse(false);
        assertEquals(1, 1);
        
    }
    
    @Test
    public final void testSubsetGeneration() {
        Set<Object> atoms = new HashSet<Object>();
        
        Object n1 = "node1";
        Object n2 = "node2";
        Object n3 = "node3";
        Object n4 = "node4";
        Object n5 = "node5";
        
        // duplicate code w/ testSimplePathGeneration
        
        atoms.add(n1); atoms.add(n2); atoms.add(n3); atoms.add(n4); atoms.add(n5);
        final Universe universe = new Universe(atoms);
        final TupleFactory factory = universe.factory();      
        // Remember to use the actual atoms here, not the sub-tuples
        Tuple tn1 = factory.tuple(n1);
        Tuple tn2 = factory.tuple(n2);
        Tuple tn3 = factory.tuple(n3);
        Tuple tn4 = factory.tuple(n4);
        Tuple tn5 = factory.tuple(n5);
        
        TupleSet ub = universe.factory().noneOf(1);
        ub.add(tn1); ub.add(tn2); ub.add(tn3); ub.add(tn4); ub.add(tn5);
        
        Set<TupleSet> res = AmalgamVisitorHelper.getNElementSubsets(3, ub); // 5 choose 3
                       
        assertEquals(10, res.size());
        for(TupleSet r : res) {
            System.err.println(r);
            assertEquals(3, r.size());
        }                
        
    }
    
    @Test
    public final void testSimplePathGeneration() {
        Set<Object> atoms = new HashSet<Object>();
        
        Object n1 = "node1";
        Object n2 = "node2";
        Object n3 = "node3";
        Object n4 = "node4";
        Object n5 = "node5";
        
        atoms.add(n1); atoms.add(n2); atoms.add(n3); atoms.add(n4); atoms.add(n5);
        final Universe universe = new Universe(atoms);
        final TupleFactory factory = universe.factory();      
      
        
//        Tuple tn1 = factory.tuple(n1);
//        Tuple tn2 = factory.tuple(n2);
//        Tuple tn3 = factory.tuple(n3);
//        Tuple tn4 = factory.tuple(n4);
//        Tuple tn5 = factory.tuple(n5);

        // Remember to use the actual atoms here, not the sub-tuples
        Tuple tn15 = factory.tuple(n1, n5);
        Tuple tn13 = factory.tuple(n1, n3);
        Tuple tn35 = factory.tuple(n3, n5);
        Tuple tn31 = factory.tuple(n3, n1);
        
        // public Set<List<Object>> buildSimplePaths(Object source, Object destination, TupleSet ub, Set<Object> seen) {
        
        TupleSet completeGraph = factory.allOf(2);
        TupleSet nullGraph = factory.noneOf(2);
        TupleSet oneDirectPath = factory.setOf(tn15);
        TupleSet oneIndirectPath = factory.setOf(tn13, tn35);
        TupleSet oneIndirectPathWithCycle = factory.setOf(tn13, tn35, tn31);
        TupleSet twoPathsWithCycle = factory.setOf(tn15, tn13, tn35, tn31);
                 
                                  
        Set<List<Object>> spaths = AmalgamVisitorHelper.buildSimplePaths(n1, n5, twoPathsWithCycle, new HashSet<Object>());        
        //System.err.println(spaths);
        assertEquals(spaths.size(), 2);
        
        spaths = AmalgamVisitorHelper.buildSimplePaths(n1, n5, nullGraph, new HashSet<Object>());        
        //System.err.println(spaths);
        assertEquals(spaths.size(), 0);
        
        spaths = AmalgamVisitorHelper.buildSimplePaths(n1, n5, oneDirectPath, new HashSet<Object>());        
        //System.err.println(spaths);
        assertEquals(spaths.size(), 1);
        
        spaths = AmalgamVisitorHelper.buildSimplePaths(n1, n5, oneIndirectPath, new HashSet<Object>());        
        //System.err.println(spaths);
        assertEquals(spaths.size(), 1);

        spaths = AmalgamVisitorHelper.buildSimplePaths(n1, n5, oneIndirectPathWithCycle, new HashSet<Object>());        
        //System.err.println(spaths);
        assertEquals(spaths.size(), 1);

        // 1 path of length 1 (direct hop)
        // 3 paths of length 2 (3c1 * 1!)
        // 6 paths of length 3 (3c2 * 2!)
        // 6 paths of length 4 (3c3 * 3!)
        // Total of 16 paths
        spaths = AmalgamVisitorHelper.buildSimplePaths(n1, n5, completeGraph, new HashSet<Object>());        
        //System.err.println(spaths);
        assertEquals(spaths.size(), 16); 

        
    }
}

