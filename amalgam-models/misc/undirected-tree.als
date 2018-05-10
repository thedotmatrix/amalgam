abstract sig Color {}

one sig Red extends Color {}
one sig Blue extends Color {}

sig Node {
	neighbors: set Node,
	color: one Color
}

fact undirected {
	neighbors = ~neighbors
	no iden & neighbors
}

fact graphIsConnected {
	all n1: Node | all n2: Node - n1 |
		n1 in n2.^neighbors
}

fact treeAcyclic {
	all n1, n2 : Node | n1 in n2.neighbors implies
		n1 not in n2.^(neighbors - (n2 -> n1))
}

fact colorSet {
	all n : Node | Blue in n.color iff lone n.neighbors
}

/*
fact arityRestrict {
	all n : Node | #(n.neighbors) <= 4
}
*/

run { } for 1 Node, 5 Int
run { } for 2 Node, 5 Int
run { } for 3 Node, 5 Int
run { } for 4 Node, 5 Int
run { } for 5 Node, 5 Int
run { } for 6 Node, 5 Int
run { } for 7 Node, 5 Int
run { } for 8 Node, 5 Int
run { } for 9 Node, 5 Int
