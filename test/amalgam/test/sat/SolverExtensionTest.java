package amalgam.test.sat;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import kodkod.engine.satlab.SolverExtension;
import kodkod.engine.satlab.SolverWrapper;

public class SolverExtensionTest {
	SolverExtension solver; 

	@Before
	public void setup() {
		solver = SolverWrapper.construct();
	}
	@After
	public void teardown() {
		solver.free();
	}

	@Test
	public void assumptions() {
		// add 6 variables
		solver.addVariables(6);
		assertEquals(6, solver.numberOfVariables());
		// the following prop theory is unsat if 1,2,3,4 are assumed false
		int[] c1 = {1,5,6};
		int[] c2 = {2,5,-6};
		int[] c3 = {3,-5,6};
		int[] c4 = {4,-5,-6};
		assertTrue(solver.addClause(c1));
		assertTrue(solver.addClause(c2));
		assertTrue(solver.addClause(c3));
		assertTrue(solver.addClause(c4));
		List<Integer> assumpsSAT = new ArrayList<>();
		List<Integer> assumpsUNSAT = new ArrayList<>(Arrays.asList(-1,-2,-3,-4));
		// make sure it's sat without assuming, unsat with, and still sat after
		assertTrue(solver.solveAndAssume(assumpsSAT));
		assertFalse(solver.solveAndAssume(assumpsUNSAT));
		assertTrue(solver.solveAndAssume(assumpsSAT));
	}
}
