/*
From Alloy HW 3
Problem 1: Directed Tree Properties
We give students the skeleton of isDirectedTree
and expect them to fill in the constraints.

TN: Changed to use Node sig rather than univ

BUG: mis-stated injectivity axiom. Manifests as:
	(1) unexpected co-existence of facts 
        caught by looking at an instance given
	(2) missing instances caught with 
        caught by test case pred that detects inconsistency      

	These do not manifest until we see 3 connected Nodes!
	(Minimality fails, but maximality will not.)

	Indeed, nothing *forces* the extra to exist.
	We might also ask "why is there NOT a branch"
*/

sig Node { edges: set Node}

// Correct version:
pred isDirectedTreeCorrect {
	-- acyclic:
	no iden & ^edges
	-- injective:
	edges.~edges in iden 
	-- connected:
	(Node -> Node) in ^(edges + ~edges)
} 

// Buggy version:
pred isDirectedTreeBug {
	-- acyclic:
	no iden & ^edges
	-- injective:
	// BUG! Flipped transpose both under- and over-
	// constrains the problem. 
	~edges.edges in iden 
	//r.~r in iden // <- this is correct
	-- connected:
	(Node -> Node) in ^(edges + ~edges)
} 

// Partial model w/o partial model primitives:
// Find me an inst containing 3 nodes that form a < tree. 
// Expect SAT. If unsat, detect overconstraint.
pred testCaseForBug {
	isDirectedTreeBug[]
	//isDirectedTreeCorrect[r]
	some disj n1, n2, n3: Node | 
		n1->n2 + n1->n3 in edges
	// [?] possible for this to be SAT but incorrectly?
	// If so, looking at instance would reveal another issue.
}

//  Has two nodes with edges into the same node;
//  non injective [Aluminum won't show]
run isDirectedTreeBug for 4 Node
//  Unsat if using buggy pred. [Aluminum detects too]
//run testCaseForBug for exactly 3 Node
