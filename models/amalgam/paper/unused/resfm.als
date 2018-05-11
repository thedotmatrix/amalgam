/*
	Buggy model of resolution (Figure 1)
	From _Finding Minimal Unsatisfiable Cores of Declarative Specifications_
	Emina Torlak, Felix Sheng-Ho Chang, and Daniel Jackson
	Formal Methods 2008	
*/

abstract sig Boolean {}
one sig True, False extends Boolean {}

sig Literal { neg : Literal }
fact { neg = ~neg and no iden & neg }

sig Clause {lits: set Literal}
one sig Conflict extends Clause{} {no lits}
fact {all c: Clause - Conflict | some c.lits}
fact {all c: Clause | no c.lits & c.lits.neg}

pred resolve[c1, c2, r: Clause] {
	some x: c1.lits & c2.lits.neg  |
		r.lits = (c1.lits & c2.lits) - (x + x.neg)
}

sig Refutation {
	sources: some Clause - Conflict,
	resolvents: set Clause,
	edges: (sources + resolvents) -> resolvents
} {
	no ^edges & iden
	all r: resolvents | some edges.r
	Conflict in resolvents

	// Buggy version
/*	all n1,n2: sources + resolvents |
		all r: resolvents |
			(n1+n2)->r in edges iff
			resolve[n1,n2,r]
*/
	// Fixed version
	edges = {
		n: sources + resolvents, r: resolvents |
			one edges.r - n and
			resolve[n, edges.r - n, r] }
}


sig Instance {
	clauses: some Clause,
	assign: Literal->lone Boolean
} {
	all lit: clauses.lits | 
		assign[lit] = Boolean - assign[lit.neg]
	all c: clauses | True in assign[c.lits]
}

-----------------------------------------------------

// IMPORTANT: switch to buggy version of sigfact above
assert case1example {
	all i: Instance |
		no ref: Refutation | 
			ref.sources = i.clauses
}
//check case1example for 3

-----------------------------------------------------

// case 2 example is case1example with fixed sigfact

-----------------------------------------------------

// case 3: weak assertion
// Run with fixed sigfact

assert case3example {
	all i: Instance, cs: set i.clauses | 
		cs in lits.(i.assign.True)
}
//check case3example for 3

-----------------------------------------------------

// case 4: scope is too small

assert case4example {
	all ref: Refutation | 
		no (ref.edges).(ref.sources)
}
//check case4example for 2
//check case4example for 3
//check case4example for 4
check case4example for 5

