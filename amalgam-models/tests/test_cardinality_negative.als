-- IMPORTANT: see tn_test_cardinality.als for notes on required integer bounds.

sig Node {edges: set Node}

pred noTwoNeighbors {
	no n : Node |
		#(n.edges) = 2
}
run noTwoNeighbors for exactly 3 Node, 3 int


pred noMoreThanTwoNeighbors {
	no n: Node | 
		#(n.edges) > 2
}
run noMoreThanTwoNeighbors for exactly 3 Node, 3 int

/*
pred allLessThanEqual2 {
	all n: Node | 
		#(n.edges) <= 2
}

pred inequalityImpliesFailingEquality {
	#Node > 2 implies 
		all n: Node | #(n.edges) = 2
}

-------------------------------------------------------------------------------



run someMoreThan2 for 3 but 4 int 


run allLessThanEqual2 for exactly 3 Node, 4 int 

run inequalityImpliesFailingEquality for exactly 3 Node, 4 int
*/
