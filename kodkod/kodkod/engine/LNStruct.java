package kodkod.engine;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

public class LNStruct {
	Integer lnLit;
	List<List<Integer>> disj;
	
	public LNStruct(Integer lnLit) {
		this.lnLit = lnLit;
		this.disj = new ArrayList<>();
	}
	
	public List<CNF> getClauses() {
		List<CNF> ret = new ArrayList<>();
		for (List<Integer> conj : disj) {
			CNF now = new CNF();
			now.addClause(Arrays.asList(lnLit));
			for (Integer e : conj) {
				now.addClause(Arrays.asList(e));
			}
			ret.add(now);
		}
		return ret;
	}

	public void addClause(List<Integer> toBeAdded) {
		disj.add(toBeAdded);
	}

	public List<Boolean> process(Set<Integer> currentModel) {
		if (!currentModel.contains(lnLit)) return null;
		//System.out.println("On " + lnLit);
		List<Boolean> branches = new ArrayList<>(disj.size());
		for (List<Integer> conj : disj) {
			boolean allTrue = true;
			for (Integer e : conj) {
				if (!currentModel.contains(e)) {
					allTrue = false;
					break;
				}
			}
			branches.add(allTrue);
		}
		return branches;
	}

	@Override
	public String toString() {
		return "(LNStruct #:lnLit " + lnLit + " #:disj " + disj + ")";
	}
}
