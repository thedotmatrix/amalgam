/*
	JUST a digraph of up to 4 nodes
*/

sig Node {edges: set Node}
pred test {some Node}
run test for 4 Node