sig Node {edges: set Node}

// Everybody has different successor sets
pred testDisj {
  no disj n1,n2: Node | n1.edges = n2.edges
}
run testDisj for 2


pred testDesugarLone {
    -- this disallows size>1 instances
    -- lone n1,n2: Node | n1.edges = n2.edges

    -- instead, say at most one distinct pair with same succ sets
	--lone n1: Node, n2: Node-n1 | n1.edges = n2.edges
	lone disj n1,n2: Node | n1.edges = n2.edges
    
}
run testDesugarLone for 2

