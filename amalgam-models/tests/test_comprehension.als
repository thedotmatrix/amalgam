sig Node {edges : set Node }

fact testComprehensionExpansion {
  some { n1, n2: Node | n1->n2 in edges}
  lone edges
}

// Ask why the lone edge is necessary
run {} for exactly 2 Node
