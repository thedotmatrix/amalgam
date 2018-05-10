/*
	Test bounds recovery on ordering.
	This specification is fully constrained, and has only one model.
	0->0->0->0
*/

open util/ordering[Node]

sig Node {edges: set Node} 

fact orderingEdges {
	all n: Node | {
		-- first node has no inflow (un-necessary with equality in 2nd constraint)
		-- first not in Node.edges 
		-- each node flows into its next (and nothing more)		
		n.next = n.edges
	}
}


run {} for 4
