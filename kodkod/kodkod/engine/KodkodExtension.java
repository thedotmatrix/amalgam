package kodkod.engine;

import kodkod.ast.Relation;
import kodkod.instance.Tuple;

/**
 * The bridge between the SAT and Alloy worlds
 * Takes first-order models (Solutions) in, 
 * picks them apart into propositional pieces,
 * and sends those to the solver.
 */
public interface KodkodExtension extends KodkodSolver {
	public Solution current();
	
	// exit the cone/anticone
	public Solution diff(); // add negation of entire diagram
	public Solution diffCone(); // add negation of pos diagram
	public Solution diffAntiCone(); // add negation of neg diagram
	
	// explore the cone/anticone
	public Solution shrink(); // add negation of pos diagram "remove something" in the anticone
	public Solution minimize(); // loop reduce
	public Solution grow(); // add negation of neg diagram "add something" in the cone
	public Solution maximize(); // loop grow
	
	// push/pull the cone/anticone up/down
	public Solution augment(Relation r, Tuple fact);
	public Solution backtrack();
}
