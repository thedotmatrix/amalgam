/*
	Homoeomorphically irreducible trees of size <10
      - is a tree (undirected)
*/

sig Node {
	edges: set Node,
}
fact tree {
	edges = ~edges   -- symmetric
	no iden & edges  -- antireflexive

	-- no cycles (can't say usual directed acyclic because symmetry!)
	all n1, n2: Node | n1 in n2.edges implies {
		n1 not in n2.^(edges-(n2->n1))
	}

	-- connected
	all n1: Node | all n2: Node-n1 | n1 in n2.^edges
}

fact homIrred {
	-- 1 ~ 2 ~ 3 => 2 must have some other out-edge
	all n1, n2, n3: Node |
		(n1 != n3 and n2 in n1.edges and n3 in n2.edges) implies
		some other : Node-(n1+n3) | other in n2.edges
}

fact nonEmpty {
	-- not, in fact, stated in the problem, but implied
	some Node
}

run {} for exactly 6 Node
