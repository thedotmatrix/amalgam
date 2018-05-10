/*
	Directed trees (irreflexive, connected, acyclic)	
	(Also serves as a test case for predicate expansion.)
*/

sig Node { edges: set Node }

pred irreflexive {
	no iden & edges
}

pred canreach[n1: Node, n2: Node] {
	n2 in n1.^edges
}

pred allreachable {
	all n1: Node, n2: Node-n1 | canreach[n1,n2]
}

pred injective {		
	edges.~edges in iden 
}

pred directedacyclic {
	no n: Node | n in n.^edges
}

pred partialTree {
	irreflexive
	allreachable
	injective
	directedacyclic
}

// To test resolving no-arg pred with multi-arg inside to also resolve, 
// "why need this edge?"
//run partialTree for 5
//run partialTree for 6
run partialTree for 7