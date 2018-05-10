/*
Provenance of why C$0 in C and why (C$0, B$0, D$0) in field are isomorphic.

If the tool does not output a model that has `(C$0, B$0, D$0)`, then users wouldn't
be able to discover the overconstraint, which is that
`all x : B | some x.field` is unintended
*/

sig A {}
sig B {}
sig D {}

one sig C {
	field: (A + B) -> D
} {
	all x : A + B | some x.field
}

run {} for 1
run {} for 2
run {} for 3
run {} for 4
run {} for 5
run {} for 6
run {} for 7
