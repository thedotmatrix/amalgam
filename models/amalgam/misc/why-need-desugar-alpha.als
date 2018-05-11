/*
Wrote: all t : T | some (t.rel & T1)
Intended: all t : TA | some (t.rel & T1)
Unintended: all t : TB | some (t.rel & T1)

However, it's possible that the model that the tool shows will be:

rel = {(TA, TA)}

Without atom TB, it's impossible to see that some (TB, TA) is LN, so users can't
discover the overconstraint
*/

abstract sig T {
	rel: set T
}
sig TA extends T {}
sig TB extends T {}

fact {
	all t : T | some (t.rel & TA)
}

run {} for 1
run {} for 2
run {} for 3
run {} for 4
run {} for 5
run {} for 6
run {} for 7
