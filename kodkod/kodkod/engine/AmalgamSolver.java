package kodkod.engine;

import java.util.Iterator;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;

public class AmalgamSolver implements KodkodExtension{
	private AmalgamCore core;
	public String strategy = null;

	public AmalgamSolver() {
		core = new AmalgamCore();
	}

	/* Core Methods */ 
	@Override
	public Options options() {
		return core.options;
	}
	@Override
	public Solution solve(Formula formula, Bounds bounds)
			throws HigherOrderDeclException, UnboundLeafException, AbortedException {
		return core.solve(formula, bounds);
	}
	@Override
	public void free() {
		core.free();
	}
	@Override
	public Solution current() {
		return core.current();
	}
	@Override
	public Solution diff() {
		return core.diff();
	}
	@Override
	public Solution diffCone() {
		return core.diffCone();
	}
	@Override
	public Solution diffAntiCone() {
		return core.diffAntiCone();
	}
	@Override
	public Solution shrink() {
		return core.shrink();
	}
	@Override
	public Solution minimize() {
		return core.minimize();
	}
	@Override
	public Solution grow() {
		return core.grow();
	}
	@Override
	public Solution maximize() {
		return core.maximize();
	}
	@Override
	public Solution augment(Relation r, Tuple fact) {
		return core.augment(r, fact);
	}
	@Override
	public Solution backtrack() {
		return core.backtrack();
	}

	public Bounds getBounds() {
		return core.translation.bounds();
	}
	public Solution getModel() {
		return core.model;
	}

	public SolutionIterator solveAll(final Formula formula, final Bounds bounds) 
			throws HigherOrderDeclException, UnboundLeafException, AbortedException {
		return new SolutionIterator(formula, bounds, this); 
	}
	public boolean usable() {
		return ((core.model.outcome() == null) || core.model.sat() == Boolean.TRUE);
	}
	public static final class SolutionIterator implements Iterator<Solution> {
		private final AmalgamSolver solver;
		private Solution s = null;
		SolutionIterator(Formula formula, Bounds bounds, AmalgamSolver solver) {
			this.solver = solver;
			solver.solve(formula, bounds);
		}
		public boolean hasNext() { return true; }
		public Solution next(String type) {
			if(type.startsWith("augment")) {
				String[] args = type.split("_");
				Bounds b = this.solver.core.translation.bounds();
				Relation rel = null;
				Tuple tup = null;
				for(Relation r : b.relations()) {
					if(r.toString().endsWith(args[1])) {
						rel = r;
					}
				}
				for(Tuple t : b.upperBound(rel)) {
					if(t.toString().equals(args[2])) {
						tup = t;
					}
				}
				s=solver.augment(rel, tup);
			} else {
				s=next();
			}
			return s;
		}
		public Solution next() {
			// if we haven't returned the translation/solved model, don't diff
			if(s==null) s=solver.current();
			else {
				// enumerate
				switch(solver.strategy) {
				case "Alloy (arbitrary models)" : {
					s=solver.diff();
					break;
				}
				case "Aluminum (minimal models)" : {
					s=solver.diffCone();
					break;
				}
				case "show me only maximal models" : {
					s=solver.diffAntiCone();
					break;
				}
				case "show me high coverage models" : {
					break;
				}
				default : throw new IllegalArgumentException("Unsupported strategy: "+solver.strategy);
				}
			}
			// refine
			switch(solver.strategy) {
			case "Alloy (arbitrary models)" : {
				break;
			}
			case "Aluminum (minimal models)" : {
				s=solver.minimize();
				break;
			}
			case "show me only maximal models" : {
				s=solver.maximize();
				break;
			}
			case "show me high coverage models" : {
				s=solver.core.coverage();
				break;
			}
			default : throw new IllegalArgumentException("Unsupported strategy: "+solver.strategy);
			}
			// if no more models, return same model as last time
			if(s==null) s=solver.current();
			return s;
		}
		public void remove() { throw new UnsupportedOperationException(); }
	}
} 
