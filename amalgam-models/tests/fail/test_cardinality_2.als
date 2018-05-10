abstract sig Node {edges: set Node}
sig BlueNode extends Node {}
sig RedNode extends Node {}

-- Test two-sided cardinality and ability to flip a sig
-- (This actually will fail because 2-sided /change/)
--fact equalNodes {
--	#GroovyNode = #(Node-GroovyNode)
--}

-- Test two-sided cardinality and ability to flip a sig
-- This is a revised version of the above: need only one
-- side to vary
fact equalNodes {
	#BlueNode = #RedNode
}

-- Test numeric expressions
fact evenEdges {
	rem[#edges, 2] = 0
}

run {} for 3 but 3 int
-- CASE:
-- Why BlueNode? (in model with a blue node)

