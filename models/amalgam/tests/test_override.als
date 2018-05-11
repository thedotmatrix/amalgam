sig Node { edgesBlue, edgesRed, edgesPurple: set Node }

fact purpleOverrides {
	edgesPurple = edgesBlue ++ edgesRed
}

fact setup {
	some n1, n2, n3: Node | {
		n1 != n2
		n2 != n3
		n1 != n3
		n1->n2 in edgesBlue
		n1->n3 in edgesRed
	}
}

run {} for exactly 3 Node
