package kodkod.engine;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SolverExtension;
import kodkod.engine.satlab.SolverWrapper;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntSet;

public final class AmalgamCore implements KodkodExtension {
	final Options options;
	SolverExtension solver;
	Translation.Whole translation;
	Solution model;
	/* invariant: all persist triggers are alive (negative) until someone calls backtrack */
	final List<Integer> persistent;
	/* invariant: all temp triggers are dead (positive) in the list after each traversal */
	final List<Integer> temporary;
	// FIXME z3 / coverage
	//boolean firstCoverage;
	AmalgamCoreHelper helper;
	//List<LNStruct> lnClauses;
	//List<CNF> workers;
	

	/* Constructor */
	public AmalgamCore(Options options)
	{
		this.options = options;
		//this.helper = null;
		this.persistent = new ArrayList<>();
		this.temporary = new ArrayList<>();
	}
	public AmalgamCore() {
		this(new Options());
	}
	
	/* Exiting Methods */
	public Solution coverage() {
		/* FIXME z3 / coverage
		if (false) {
			//firstCoverage = false;
			List<Integer> reducedLits = 
					ReduceLiterals.getIntLits(this.translation);
			Set<Integer> reducedLitsSet = new HashSet<>(reducedLits);
			
			System.out.println("Representative: " + reducedLitsSet);
			
			List<List<Integer>> satClauses = solver.getClauses();
			List<Integer> thatClause = satClauses.get(satClauses.size() - 2);
			assert thatClause.size() == 1;
			int topLit = thatClause.get(0);
			List<List<Integer>> realSatClauses = new ArrayList<>();
			
			for (List<Integer> clause : satClauses) {
				boolean skip = false;
				for (Integer lit : clause) {
					if (lit > topLit) {
						skip = true;
						break;
					}
				}
				if (!skip) {
					realSatClauses.add(clause);
				}
			}
			
			lnClauses = AmalgamCoreHelper.getLNClauses(
					new CNF(satClauses),
					reducedLitsSet);
			
			List<List<CNF>> workersGroup = new ArrayList<>();
			
			workers = new ArrayList<>();
			
			for (LNStruct lnClause : lnClauses) {
				workersGroup.add(lnClause.getClauses());
				//workers.addAll(lnClause.getClauses());
			}
			
			while (!workersGroup.isEmpty()) {
				List<CNF> group = workersGroup.remove(0);
				if (group.isEmpty()) continue;
				workers.add(group.remove(group.size() - 1));
				workersGroup.add(group);
			}
		}
		List<List<Integer>> diffClauses = new ArrayList<>();
		// add the negation of the diagram
		diffClauses.add(Translate.union(this.getPrimaryDiagram(true, true), this.getPrimaryDiagram(false, false)));
		Integer trigPerm = solver.registerClauses(diffClauses);
		this.persistent.add(-trigPerm);
		/*
		while (!workers.isEmpty()) {
			/*
			CNF currentWorker = workers.get(0);
			System.out.println(currentWorker.getClauses().get(0));
			Integer trig = solver.registerClauses(currentWorker.getClauses());
			if (trig == 0) {
				workers.remove(0);
				continue;
			}
			this.temporary.add(-trig);
			solve(0);
			this.temporary.remove(this.temporary.size() - 1);
			if (model.sat()) {
				break;
			} else {
				System.out.println("removing");
				workers.remove(0);
			}
			*/
			/*
			CNF currentWorker = workers.remove(0);
			
			translation.options().reporter().reportCurrentLit(currentWorker.getClauses().get(0).get(0));
			//System.out.println();
			Integer trig = solver.registerClauses(currentWorker.getClauses());
			if (trig == 0) continue;
			this.temporary.add(-trig);
			solve(0);
			this.temporary.remove(this.temporary.size() - 1);
			if (model.sat()) {
				workers.add(currentWorker);
				break;
			}
			*/
		/*
		}
		Set<Integer> currentModel = new HashSet<>(getFullDiagram());
		List<List<Boolean>> now = new ArrayList<>();
		for (LNStruct lnClause : lnClauses) {
			List<Boolean> nowSub = lnClause.process(currentModel);
			now.add(nowSub);
		}
		solve(0);
		*/
		return model;
	}
	public Solution diff() {
		List<List<Integer>> diffClauses = new ArrayList<>();
		// add the negation of the diagram
		diffClauses.add(Translate.union(this.getPrimaryDiagram(true, true), this.getPrimaryDiagram(false, false)));
		return this.traverse(diffClauses, true);
	}
	public Solution diffCone() {
		List<List<Integer>> diffClauses = new ArrayList<>();
		// add the negation of the positive diagram
		diffClauses.add(this.getPrimaryDiagram(true, true));
		return this.traverse(diffClauses, true);
	}
	public Solution diffAntiCone() {
		List<List<Integer>> diffClauses = new ArrayList<>();
		// add the negation of the negative diagram
		diffClauses.add(this.getPrimaryDiagram(false, false));
		return this.traverse(diffClauses, true);
	}
	/* Exploration Methods */
	public Solution shrink() {
		List<List<Integer>> reduceClauses = new ArrayList<>();
		// add the anticone
		List<Integer> nnd = this.getPrimaryDiagram(true, false);
		for(int i : nnd) {
			reduceClauses.add(new ArrayList<>(Arrays.asList(i)));
		}
		// add the negation of the positive diagram
		reduceClauses.add(this.getPrimaryDiagram(true, true));
		// explore a new model down the anticone of the current model
		return this.traverse(reduceClauses, false);
	}
	public Solution grow() {
		List<List<Integer>> growClauses = new ArrayList<>();
		// add the cone
		List<Integer> ppd = this.getPrimaryDiagram(false, true);
		for(int i : ppd) {
			growClauses.add(new ArrayList<>(Arrays.asList(i)));
		}
		// add the negation of the negative diagram
		growClauses.add(this.getPrimaryDiagram(false, false));
		// explore a new model up the cone of the current model
		return this.traverse(growClauses, false);
	}
	public Solution augment(Relation r, Tuple t) {
		List<List<Integer>> augClauses = new ArrayList<>();
		// add the CNF literal that maps to the given fact
		List<Integer> augment = new ArrayList<>();
		IntSet s = translation.primaryVariables(r);
		assert(s != null);
		TupleSet upperBound = this.translation.bounds().upperBound(r);
		assert(upperBound != null);
		int[] lits = upperBound.indexView().toArray();
		TupleFactory factory = this.translation.bounds().universe().factory();
		for(int l = 0; l < lits.length; l++) {
			if(t.equals(factory.tuple(r.arity(), lits[l]))) {
				augment.add(s.min()+l);
			}
		}
		assert(augment.size()==1);
		augClauses.add(augment);
		List<Integer> ppd = this.getPrimaryDiagram(false, true);
		for(int i : ppd) {
			augClauses.add(new ArrayList<>(Arrays.asList(i)));
		}
		// explore a new model up the cone of the current model
		return this.traverse(augClauses, true);
	}
	public Solution backtrack() {
		final long startTransl = System.currentTimeMillis();
		int alive = this.persistent.remove(this.persistent.size()-1);
		this.temporary.add(-alive);
		final long endTransl = System.currentTimeMillis();
		this.solve(endTransl-startTransl);
		return model;
	}
	public Solution loop(Runnable explore) {
		Solution secondToLast = null;
		while(model.sat() && !model.equals(secondToLast))
		{
			secondToLast = model;
			explore.run();
		}
		if(secondToLast!=null) model = secondToLast;
		solver.setSAT(model.sat());
		return secondToLast;
	}
	public Solution minimize() { return this.loop(new Runnable() {
		@Override
		public void run() {
			AmalgamCore.this.shrink();
		}
	}); }
	public Solution maximize() { return this.loop(new Runnable() {
		@Override
		public void run() {
			AmalgamCore.this.grow();
		}
	}); }


	/* Helpers */
	Solution traverse(List<List<Integer>> clauses, boolean persists) {
		final long startTransl = System.currentTimeMillis();
		// add the clauses and get the new trigger
		Integer trig = solver.registerClauses(clauses);
		final long endTransl = System.currentTimeMillis();
		// add the trigger
		if (persists) this.persistent.add(-trig);
		else this.temporary.add(-trig);
		// solve given all assumptions
		this.solve(endTransl-startTransl);
		// kill the non-persistent trigger
		if (!persists)
		{
			int alive = this.temporary.remove(this.temporary.size()-1);
			this.temporary.add(-alive);
		}
		// check trigger invariants
		assert(this.persistent.stream().allMatch(t -> t < 0));
		assert(this.temporary.stream().allMatch(t -> t > 0));
		return model;
	}
	void solve(long transTime) throws AbortedException {
		try {
			translation.options().reporter().solvingCNF(translation.numPrimaryVariables(), solver.numberOfVariables(), solver.numberOfClauses());
			// Solve using the SAT solver
			final long startSolve = System.currentTimeMillis();
			boolean sat = solver.solveAndAssume(Translate.union(persistent, temporary));
			final long endSolve = System.currentTimeMillis();
			// Record the stats
			final Statistics stats = new Statistics(translation, transTime, endSolve - startSolve);
			// track the latest solution
			if (sat) model = Solution.satisfiable(stats, translation.interpret());
			else model = Solution.unsatisfiable(stats, new ResolutionBasedProof(solver, translation.log()));
		} 
		// Abort if anything went wrong
		catch (SATAbortedException sae) {
			free();
			throw new AbortedException(sae);		
		} catch (RuntimeException e) {
			free();
			throw e;
		}
	}
	// sign is true for positive diagram, false for negative diagram
	// negateVars will change the sign of the variables
	List<Integer> getPrimaryDiagram(boolean negateVars, boolean sign) {
		List<Integer> diagram = new ArrayList<>();
		for (int i=1; i<=translation.numPrimaryVariables(); i++)
		{
			// diagram must not contain the assumption triggers
			if(!this.temporary.contains(i) && !this.temporary.contains(-i) && solver.valueOf(i)==sign)
			{
				if(negateVars) diagram.add(-i);
				else diagram.add(i);
			}
		}
		return diagram;
	}
	List<Integer> getFullDiagram() {
		List<Integer> diagram = new ArrayList<>();
		for (int i=1; i<=solver.numberOfVariables(); i++)
		{
			int v = solver.valueOf(i) ? i : -i;
			diagram.add(v);
		}
		return diagram;
	}
	public Solution current() { return this.model; }
	public Set<Integer> getTriggers() { 
		Set<Integer> trigs = new HashSet<>();
		for(int v : Translate.union(persistent, temporary)) {
			trigs.add(-Math.abs(v));
		}
		return trigs;
	}

	/* KodKod Methods */
	// This is like the origin point for the model space
	public Solution solve(Formula f, Bounds b) throws HigherOrderDeclException, UnboundLeafException, AbortedException {
		// FIXME z3 / coverage currently breaking all design patterns
		//firstCoverage = false;
		//this.helper = new AmalgamCoreHelper(solver);
		// Translate to CNF		
		final long startTransl = System.currentTimeMillis();
		translation = Translator.translate(f, b, this.options);				
		final long endTransl = System.currentTimeMillis();
		solver = new SolverWrapper(this.options, translation.cnf());
		// if the translation is trivial, no need to SAT solve
		if(translation.trivial())
		{
			final Statistics stats = new Statistics(translation, endTransl - startTransl, 0);
			model = solver.numberOfClauses()==0 ? Solution.triviallySatisfiable(stats, translation.interpret()) : Solution.triviallyUnsatisfiable(stats, new TrivialProof(translation.log())); 
		}
		// non-trivial translation, sat solve 
		else this.solve(endTransl - startTransl); 
		return model;
	}
	public Options options() { return this.options; }
	public void free() { }
}

