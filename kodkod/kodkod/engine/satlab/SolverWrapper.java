package kodkod.engine.satlab;

import java.util.List;
import java.util.Map;

import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.config.Options;

public class SolverWrapper implements SolverExtension {
	MiniSatProver solver;
	Boolean sat;

	public SolverWrapper(Options options, SATSolver solver) {
		if(!options.solver().instance().getClass().equals(solver.getClass()))
			throw new RuntimeException("Options don't match solver given: ");
		if(!(solver instanceof MiniSatProver))
			throw new RuntimeException("Amalgam only supports MiniSatProver for now");
		this.solver = (MiniSatProver) solver;
	}
	public static SolverWrapper construct() {
		Options options = new Options();
		options.setSolver(SATFactory.MiniSatProver);
		return new SolverWrapper(options, SATFactory.MiniSatProver.instance());
	}

	
	/* Extended Methods */
	@Override
	public boolean solveAndAssume(List<Integer> assumps) {
		this.sat = this.solver.solveAndAssume(solver.peer(), this.toPrimitive(assumps));
		this.setSAT(this.sat);
		return this.sat;
	}
	@Override
	public Integer registerClauses(List<List<Integer>> clauses) {
		boolean clausesAdded = false;
		// create a new trigger variable
		this.addVariables(1);
		int trig = this.numberOfVariables();
		// mark each clause with the trigger and add them
		for(List<Integer> clause : clauses) {
			int[] c = this.toPrimitive(clause);
			// mark the clause
			int[] marked = new int[c.length+1];
			for(int j=0; j<c.length; j++) {
				marked[j] = c[j];
			}
			marked[c.length] = trig;
			// add the marked clause
			clausesAdded |= this.addClause(marked);
		}
		// addClause returns false if the clause was already present
		// can't expect all add calls to return true
		// making sure AT LEAST ONE is true
		if(!clausesAdded) {
			System.out.println("Warning: register fails");
			return 0;
		}
		return trig;
	}
	@Override
	public List<List<Integer>> getClauses() {
		return this.solver.clauses;
	}
	@Override
	public Map<Integer, BooleanFormula> sVarFolder() {
		return this.solver.sVarFolder;
	}
	
	
	/* Prover Methods */
	@Override
	public ResolutionTrace proof() {
		return this.solver.proof();
	}
	@Override
	public void reduce(ReductionStrategy strategy) {
		this.solver.reduce(strategy);
	}
	/* Solver methods */
	@Override
	public int numberOfVariables() {
		return this.solver.numberOfVariables();
	}
	@Override
	public int numberOfClauses() {
		return this.solver.numberOfClauses();
	}
	@Override
	public void addVariables(int numVars) {
		this.solver.addVariables(numVars);
	}
	@Override
	public boolean addClause(int[] lits) {
		return this.solver.addClause(lits);
	}
	@Override
	public boolean addClause(int[] lits, BooleanFormula circuit) { return this.addClause(lits); }
	@Override
	public boolean solve() throws SATAbortedException {
		return this.solver.solve();
	}
	@Override
	public boolean valueOf(int variable) {
		return this.solver.valueOf(variable);
	}
	@Override
	public void free() {
		this.solver.free();
	}
	
	
	/* Helpers */
	int[] toPrimitive(List<Integer> list) {
		int[] prim = new int[list.size()];
		for(int i=0;i<list.size();i++) {
			prim[i] = list.get(i);
		}
		return prim;
	}
	@Override
	public void setSAT(boolean sat) {
		this.solver.sat = sat;
	}
}
