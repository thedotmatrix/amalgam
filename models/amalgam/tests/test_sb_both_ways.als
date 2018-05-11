sig Node { edges: set Node }

// no immediate self loops
run { no edges & iden } for exactly 2 Node expect 0
run { no edges & iden } for exactly 2 Node expect 1

