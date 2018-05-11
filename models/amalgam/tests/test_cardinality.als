sig Node {edges: set Node}

pred allTwoNeighbors {
	all n : Node |
		#(n.edges) = 2
}

pred someMoreThan2 {
	some n: Node | 
		#(n.edges) > 2
}

pred allLessThanEqual2 {
	all n: Node | 
		#(n.edges) <= 2
}

pred inequalityImpliesFailingEquality {
	#Node > 2 implies 
		all n: Node | #(n.edges) = 2
}

-------------------------------------------------------------------------------

-- If we do this, Alloy creates bitwidth=3 even if it doesn't need to.
-- Integer evaluation now works (4 --> {4}).
run allTwoNeighbors for 4 but 3 int

-- If we do this, the constant 2 will be compiled out and Alloy 
-- will detect it doesn't need integers, resulting in bitwidth=0.
-- N.B. this breaks evaluation of integer expressions! Moreover
-- we cannot just detect the constant, because there will not
-- be a tuple we can map it to (since integers were compiled out).

--run allTwoNeighbors for 4

-- ^ Amalgam DOES NOT SUPPORT the above.

-- Test greater-than desugaring with a non-trivial bitwidth
-- (if 3 int, only the integer 3 is large enough)
run someMoreThan2 for 3 but 4 int 


run allLessThanEqual2 for exactly 3 Node, 4 int 

run inequalityImpliesFailingEquality for exactly 3 Node, 4 int
