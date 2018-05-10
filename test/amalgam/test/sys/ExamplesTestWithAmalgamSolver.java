package amalgam.test.sys;

import java.util.ArrayList;
import java.util.Collection;

import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import kodkod.ast.Formula;
import kodkod.engine.AmalgamCore;
import kodkod.engine.Solution;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

//import kodkod.test.util.Solvers;

@RunWith(Parameterized.class)
public class ExamplesTestWithAmalgamSolver extends ExamplesTest  {


	private final AmalgamCore solver;
	
	public ExamplesTestWithAmalgamSolver(SATFactory solverOpt) {
		this.solver = new AmalgamCore();
		//this.solver.options().setSolver(solverOpt);
	}
	
	@Parameters
	public static Collection<Object[]> solversToTestWith() {
		final Collection<Object[]> ret = new ArrayList<Object[]>();
//		for(SATFactory factory : Solvers.allAvailableSolvers()) {
//			ret.add(new Object[]{factory});
//			//System.out.println(factory);
//		}
		ret.add(new Object[]{SATFactory.MiniSatProver});
		return ret;
	}

	protected Solution solve(Formula formula, Bounds bounds) {
		return solver.solve(formula, bounds);
	}
}
