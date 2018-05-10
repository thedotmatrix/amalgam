abstract sig Person {
	supervises: set Person,
	grad: one School
}
one sig Alice extends Person {}
one sig Bob extends Person {}
one sig Charlie extends Person {}

abstract sig School {}
one sig Brown extends School {}
one sig NotBrown extends School {}

fact {
	supervises = Alice->Bob + Bob->Charlie
	// Note: change this to equality and you can
	// see something is suspicious: small core.
	Alice->Brown + Charlie->NotBrown in grad
}

assert bgSupnbg {
	some bg: grad.Brown | 
	some nbg: grad.NotBrown |
		nbg in bg.supervises
}
//check bgSupnbg

run {}
