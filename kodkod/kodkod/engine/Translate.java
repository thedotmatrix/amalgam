package kodkod.engine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.TranslationRecord;
import kodkod.engine.satlab.Clause;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

/**
 * Any helper function created due to awkward type translation between...
 * 
 * First order and prop logic
 * int[] and List<Integer>
 * Clauses and literal arrays
 * etc
 * 
 * ..go here
 */
// XXX this class probably shouldnt exist. this is a graveyard of loose data couplings...
public class Translate {
	private Translation.Whole trans;
	public Map<Integer, Relation> pvm;
	public Map<Integer, String> svm;
	public Set<Integer> noEnvSecondaries = new HashSet<>();
	// XXX really ugly!!!
	public Map<Object, String> atom2name = new HashMap<>();
	
	public Translate(Translation.Whole t) {
		this.trans = t;
		// primary var map
		pvm = new HashMap<>();
		for(Relation r : t.bounds().relations())
		{
			IntSet varsForThisRelation = t.primaryVariables(r);

			//if there is no primary variable for this relation, continue:
			if(varsForThisRelation == null)
				continue;

			IntIterator itVarsForThis = varsForThisRelation.iterator();
			while(itVarsForThis.hasNext())
			{
				int v = itVarsForThis.next();
				pvm.put(v, r);
			}
		}
		// secondary var map
		svm = new HashMap<>();
		Iterator<TranslationRecord> itlog = t.log().replay();
		TranslationRecord rec;
		while(itlog.hasNext()) {
			rec = itlog.next();
			Node trans = rec.translated();
			// XXX instantiate env instead of tacking it on
			svm.put(Math.abs(rec.literal()), trans+""+rec.env());
			if(rec.env().isEmpty()) {
				noEnvSecondaries.add(Math.abs(rec.literal()));
			}
		}
	}
	
	public LinkedHashSet<Node> pCore(Set<Integer> literals) {
		LinkedHashSet<Node> pCore = new LinkedHashSet<>();
		Iterator<TranslationRecord> itlog = trans.log().replay();
		TranslationRecord rec;
		while(itlog.hasNext()) {
			rec = itlog.next();
			int l = rec.literal();
			// XXX how to filter
			if(literals.contains(l)) {
				pCore.add(rec.translated());
			}
		}
		return pCore;
	}
	
	public boolean isPrimary(int l) {
		return pvm.containsKey(Math.abs(l));
	}
	public boolean isSecondary(int l) {
		return svm.containsKey(Math.abs(l));
	}
	public boolean isTopLevelSecondary(int l) {
		return svm.containsKey(Math.abs(l)) && noEnvSecondaries.contains(Math.abs(l));
	}
	
	// TODO: skolem bounds not necessarily passed in translation. May need to extract from reporter.
	public int getPropVariableForTuple(Relation r, Tuple t) {		
		IntSet s = trans.primaryVariables(r);
		assert(s != null);
		TupleSet upperBound = trans.bounds().upperBound(r);
		assert(upperBound != null);
		int[] lits = upperBound.indexView().toArray();
		TupleFactory factory = trans.bounds().universe().factory();
		for(int l = 0; l < lits.length; l++) {
			if(t.equals(factory.tuple(r.arity(), lits[l]))) {
				return s.min()+l;
			}
		}		
		return 0;
		//throw new Exception("no prop variable for that tuple; needs better exception");
	}
	public Tuple getTupleForPropVariable(Relation r, int theVar)
	{
		IntSet s = trans.primaryVariables(r);
		// The relation's upper bound has a list of tuple indices. The "index" variable below is an index
		// into that list of indices. (If our upper bound was _everything_, would be no need to de-reference.)
		int minVarForR = s.min();

		// Compute index: (variable - minvariable) of this relation's variables 
		int index = theVar - minVarForR;

		// OPT: How slow is this? May want to cache...
		int[] arr = trans.bounds().upperBound(r).indexView().toArray();

		TupleFactory factory = trans.bounds().universe().factory();   
		Tuple tup = factory.tuple(r.arity(), arr[index]);  

		//MCommunicator.writeToLog("\ngetTupleForPropVariable: thisTuple="+tup+" for "+theVar+". Relation had vars: "+s+" and the offset was "+minVarForR+
		//		"leaving index="+index+". Upper bound indexview: "+Arrays.toString(arr)+
		//		"\nThe de-referenced tuple index is: "+arr[index]);

		return tup;
	}
	
	public String clauseToString(List<Integer> clause) {
		String out = "";
		List<Integer> neg = new ArrayList<>();
		List<Integer> pos = new ArrayList<>();
		for(int v : clause) {
			if(v<0) neg.add(v);
			else pos.add(v);
		}
		for(int n : neg) {
			out += "~"+varToString(Math.abs(n))+" /\\ ";
		}
		if(!neg.isEmpty()) out = out.substring(0, out.length()-3);
		out += "=> ";
		for(int p : pos) {
			out += varToString(p)+" \\/ ";
		}
		if(!pos.isEmpty()) out = out.substring(0, out.length()-3);
		return out; 
	}
	public String varToString(int v, Map<Integer, BooleanFormula> sVarFolder, boolean alloyNames) {
		String out = "";
		// add sign
		if(v<0) out+="~";
		v = Math.abs(v);
		// primary
		if(pvm.containsKey(v))
		{
			Relation r = pvm.get(v);
			out += r.toString();
			Tuple t = getTupleForPropVariable(r, v);
			List<String> atoms = new ArrayList<>();
			for(int i=0; i<t.arity(); i++) {
				Object atom = t.atom(i);
				if(alloyNames&&atom2name.containsKey(atom)) atom = atom2name.get(atom);
				atoms.add(atom.toString());
			}
			out += atoms; 
		}
		// secondary
		else if(svm.containsKey(v)){
			out += svm.get(v);
		}
		else if(sVarFolder.containsKey(v)) {
			out += sVarFolder.get(v);
		}
		else {
			out += v;
		}
		return out;
	}
	public String varToString(int v, boolean alloynames) {
		return varToString(v, new HashMap<Integer, BooleanFormula>(), alloynames);
	}
	public String varToString(int v, Map<Integer, BooleanFormula> sVarFolder) {
		return varToString(v, sVarFolder, false);
	}
	public String varToString(int v) {
		return varToString(v, new HashMap<Integer, BooleanFormula>(), false);
	}
	
	
	
	public static boolean clauseEqual(Clause a, Clause b) {
		int[] as = a.toArray();
		int[] bs = b.toArray();
		boolean equal = true;
		for(int i=0;i<a.size()&&i<b.size();i++) {
			equal &= as[i]==bs[i];
		}
		return equal;
	}
	public static List<Integer> union(List<Integer> lista, List<Integer> listb) {
		List<Integer> u = new ArrayList<>();
		u.addAll(lista);
		u.addAll(listb);
		return u;
	}
}
