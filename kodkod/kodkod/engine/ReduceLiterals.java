package kodkod.engine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import kodkod.ast.Relation;
import kodkod.engine.fol2sat.SymmetryDetector;
import kodkod.engine.fol2sat.Translation;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.ints.IntSet;

public class ReduceLiterals {
    static List<List<Integer>> getParts(Bounds b) {
        List<List<Integer>> parts = new ArrayList<>();
        for (IntSet part : SymmetryDetector.partition(b)) {
        	System.out.println("Partition: " + part);
            int lits[] = part.toArray();
            List<Integer> lst = new ArrayList<>(lits.length);
            
            // add this in reverse order to make it match with how Kodkod adds SBP
            for (int i = lits.length - 1; i >= 0; i--) {
                lst.add(lits[i]);
            }
            parts.add(lst);
        }
        return parts;
    }
    
    public static List<Integer> getIntLits(Translation.Whole translation) {
        Bounds b = translation.bounds();
        Universe universe = b.universe();
        List<List<Integer>> parts = getParts(b);
        Map<Integer, Integer> atomIntToPartID = new HashMap<>();
        for (int partId = 0; partId < parts.size(); partId++) {
            for (Integer atom : parts.get(partId)) {
                atomIntToPartID.put(atom, partId);
            }
        }
        Map<Relation, TupleSet> upperBounds = b.upperBounds();
        List<Integer> keepLits = new ArrayList<>();
        for (Relation r : upperBounds.keySet()) {
        	
        	System.out.println("Relation: " + r);
        	
            IntSet s = translation.primaryVariables(r);
            TupleSet ts = upperBounds.get(r);
            Iterator<Tuple> iter = ts.iterator();
            
            if (s.isEmpty() && iter.hasNext()) {
                continue;
            }
            
            while (iter.hasNext()) {
                Tuple t = iter.next();
                int lit = -1;
                int[] lits = ts.indexView().toArray();
                TupleFactory factory = universe.factory();
                for(int l = 0; l < lits.length; l++) {
                    if(t.equals(factory.tuple(r.arity(), lits[l]))) {
                        lit = s.min() + l;
                        break;
                    }
                }
                assert lit != -1;
                
                System.out.println("Literal: " + t + " " + lit);
                
                List<Integer> high = new ArrayList<>(parts.size());
                for (int i = 0; i < parts.size(); i++) high.add(0);
                
                boolean keep = true;
                for (int i = 0; i < t.arity(); i++) {
                    int litI = universe.index(t.atom(i));
                    int partId = atomIntToPartID.get(litI);
                    if (parts.get(partId).indexOf(litI) > high.get(partId)) {
                        keep = false;
                        break;
                    }
                    high.set(partId, high.get(partId) + 1);
                }
                
                if (keep) {
                    keepLits.add(lit);
                }
            }
        }
        return keepLits;
    }
}
