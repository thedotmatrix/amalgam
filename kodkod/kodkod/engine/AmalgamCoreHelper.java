package kodkod.engine;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.engine.satlab.SolverExtension;

public class AmalgamCoreHelper {
	SolverExtension solver;
	
	public AmalgamCoreHelper(SolverExtension solver) {
		this.solver = solver;
	}
	
	Integer addVariable() {
		solver.addVariables(1);
		return solver.numberOfVariables(); 
	}
	
	List<List<Integer>> DNF2CNF(List<List<Integer>> clauses) {
		List<List<Integer>> ret = new ArrayList<>();
		
		Integer topSecondary = addVariable();
		List<Integer> last = new ArrayList<>(clauses.size() + 1);
		for (List<Integer> clause : clauses) {
			Integer secondary = addVariable();
			List<Integer> lastSub = new ArrayList<>(clause.size() + 1);
			for (Integer lit : clause) {
				ret.add(Arrays.asList(lit, -secondary));
				lastSub.add(-lit);
			}
			lastSub.add(secondary);
			ret.add(lastSub);
			
			ret.add(Arrays.asList(-secondary, topSecondary));
			last.add(secondary);
		}
		last.add(-topSecondary);
		ret.add(last);
		return ret;
	}
	
	public static List<LNStruct> getLNClauses(
			CNF cnf, Set<Integer> reducedLitsSet) {
		Map<Integer, LNStruct> map = new HashMap<>();
		for (List<Integer> clause : cnf.getClauses()) {
			List<Integer> flippedClause = new ArrayList<>(clause.size());
			for (Integer lit : clause) 
				flippedClause.add(-lit);
			for (Integer lit : flippedClause) {
				if (reducedLitsSet.contains(Math.abs(lit))) {
					LNStruct val = null;
					if (map.containsKey(-lit)) {
						val = map.get(-lit);
					} else {
						val = new LNStruct(-lit);
						map.put(-lit, val);
					}
					List<Integer> toBeAdded = new ArrayList<>(flippedClause);
					toBeAdded.remove(lit);
					val.addClause(toBeAdded);
				}
			}
		}
		return new ArrayList<>(map.values());
	}
}
