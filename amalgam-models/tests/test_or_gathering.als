/*
	Test that negative literals within OR are being 
	gathered properly. To test this we need a negative
	literal that isn't the literal being flipped.
*/

sig Node {edges: set Node}
one sig NodeA extends Node {}
one sig NodeB extends Node {}

-- Avoid confusing extra models
fact antireflexive {
	no n: Node | n in n.edges
}

pred disjunction_form_1 {
	not ((NodeA -> NodeB) in edges)
	or 
	(NodeB -> NodeA) in edges
}

pred disjunction_form_2 {
	(NodeA -> NodeB) not in edges	
	or 
	(NodeB -> NodeA) in edges
}


-- in both cases:
-- @why NodeB -> NodeA
--  should produce a single provenance with:
/*
(1) ! this/NodeA -> this/NodeB !in (this/Node <: edges)
    (alternatively: this/NodeA -> this/NodeB in (this/Node <: edges))
(2) NodeB$0 -> NodeA$0 in this/NodeB -> this/NodeA
*/

-- prevent first branch from working: gives us the model we want
pred force_second_branch {
	NodeA -> NodeB in edges
}

pred test_one {
	force_second_branch
	disjunction_form_1
}
run test_one for 2 Node

pred test_two {
	force_second_branch
	disjunction_form_2
}
run test_two for 2 Node
