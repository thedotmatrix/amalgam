sig Node { edges: set Node }

fact oneDepartureNode {
	one n: Node | some n.edges
}

// Can never have zero destinations due to the above fact, but test desugaring of lone Qt
fact loneDestination {
	lone n: Node | some edges.n
}


// To test desugaring, ask why NOT some inconsistent edge (requires >1 Node)
// Model: One self-loop, one disconnected (3rd model for me)
//  Why not disconnected to self-loop? (violates oneDepartureNode)
//  Why not self-loop to disconnected? (violates loneDestination)
run {} for 3
