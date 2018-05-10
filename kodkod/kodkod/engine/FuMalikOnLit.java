package kodkod.engine;

import java.util.ArrayList;
import java.util.List;

import kodkod.util.ints.IntIterator;

public class FuMalikOnLit {
	AmalgamCore core;
	Integer lnLit;
	List<CNF> softs;
	Integer triggerForLit;
	List<Integer> auxVars;
	
	public FuMalikOnLit(
			AmalgamCore core,
			Integer lnLit,
			List<CNF> softs) {
		this.lnLit = lnLit;
		this.softs = softs;
		this.triggerForLit = core.helper.addVariable();
		this.auxVars = new ArrayList<>(softs.size());
		this.core = core;
		for (CNF soft : softs) {
			Integer auxVar = core.solver.registerClauses(
					soft.or(triggerForLit).getClauses());
			if (auxVar != 0) {
				auxVars.add(auxVar);
			} else {
				System.out.println(
						"Warning: register fails at "
						+ soft.or(triggerForLit).getClauses());
			}
		}
	}

	public int run() {
		core.temporary.add(lnLit);
		int ans = run1();
		core.temporary.remove(core.temporary.size() - 1);
		return ans;
	}
	
	int run1() {
		core.solve(0);
		if (core.model.unsat()) return 0;
		core.temporary.add(-triggerForLit);
		int ans = run2();
		core.temporary.remove(core.temporary.size() - 1);
		return ans;
	}

	int run2() {
		int cnt = 0;
		while (true) {
			if (runStep()) return softs.size() - cnt;
			cnt++;
		}
	}

	boolean runStep() {
		for (Integer auxVar : auxVars) core.temporary.add(-auxVar);
		boolean ans = runStep1();
		for (int i = 0; i < auxVars.size(); i++)
			core.temporary.remove(core.temporary.size() - 1);
		return ans;
	}
	
	boolean runStep1() {
		core.solve(0);
		if (core.model.sat()) return true;
		System.out.println("dsadsa");
		core.solve(0);
		if (core.model.sat()) return true;
		IntIterator it = core.solver.proof().core().iterator();
		while (it.hasNext()) {
			System.out.println(core.solver.proof().get(it.next()));
		}
		System.out.println("dsadsa123213");
		core.solve(0);
		if (core.model.sat()) return true;
		System.out.println("dsadsa12321334343543");
		return false;
	}
	
	

}
