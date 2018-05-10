package kodkod.engine.satlab;

import java.util.List;
import java.util.Map;

import kodkod.engine.bool.BooleanFormula;

/* 
 * Extension to the SATSolver / SATProver to expose more of the SAT functionality
 * I don't want to mess with Emina's SATFactory and translation design stuff
 * So for now, we'll just *cast* to this interface, knowing we implemented it for MinisatProver
 * Once we want to target multiple provers, we'll figure out a design pattern
 */
public interface SolverExtension extends SATProver {
	public Integer registerClauses(List<List<Integer>> clauses);
	public boolean solveAndAssume(List<Integer> assumps);
	public void setSAT(boolean sat);
	public List<List<Integer>> getClauses();
	public Map<Integer, BooleanFormula> sVarFolder(); 
	public int numberOfVariables();
	public void addVariables(int numVars);
}
