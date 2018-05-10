package kodkod.engine;

import java.util.ArrayList;
import java.util.List;

public class CNF {
	List<List<Integer>> cnf;
	
	public CNF() {
		this.cnf = new ArrayList<>();
	}
	
	public CNF(List<List<Integer>> cnf) {
		this.cnf = new ArrayList<>();
		for (List<Integer> clause : cnf) {
			this.cnf.add(new ArrayList<>(clause));
		}
	}
	
	CNF or(Integer x) {
		for (List<Integer> clause : cnf) clause.add(x);
		return this;
	}
	CNF addClause(List<Integer> clause) {
		cnf.add(clause);
		return this;
	}
	CNF removeClause(List<Integer> clause) {
		cnf.remove(clause);
		return this;
	}
	
	List<List<Integer>> getClauses() {
		return cnf;
	}
}
