abstract sig Memory {}
sig HeapCell extends Memory {}
one sig Stack extends Memory {}

// 1. What is the appropriate type for references?
// 2. What is the appropriate type for allocated?
// 6. What is the appropriate type for ref_count?
// 7. How do we set ref_count properly NO TRANS CLOSURE
abstract sig State {
	allocated: set HeapCell,
	references: Memory -> set HeapCell,
}
one sig StateA, StateB, StateC extends State {}

fun ref_count[s: State, cell: HeapCell]: Int {
  #(cell[s.references])
}

// 3. What does reachableFromStack look like?
pred stackReachable[m : Memory, state : State] {
	m in Stack.^(state.references)
}

/*
4. A memory state is safe if no unallocated memory 
is reachable from the Stack NO TRANS CLOSURE USE PRED
*//* 
A memory management system is sound if acting on an 
initial safe memory state implies that the 
following state will also be safe:
*/
pred safe[state : State] {
	all m : HeapCell | stackReachable[m,state] => m in state.allocated
}
//check soundness {
//    safe[StateA] => safe[StateC]
//} for 4 Memory

/*
5. A memory state is clean if no memory that is 
unreachable is also marked as allocated. NO TRANS CLOSURE USE PRED
*/
/*
A memory management system is complete if acting on 
an initial clean memory state implies that the 
following state will also be totally collected:
*/
pred clean[state : State] {
	all m : HeapCell |  m in state.allocated => stackReachable[m,state]
}
pred complete {
    clean[StateA] => clean[StateC]
} 
check completeness {complete} for 6 Memory, 4 Int

/* 
8. Between StateA and StateB, the program 
may create or destroy references, no allocation
*/
fact A_to_B_AllocatedUnchanged {
	StateA.allocated = StateB.allocated
}

/*
9. Between StateB and StateC, references should not change. 
The set of allocated may change as a result of garbage collection. 
A reference counting collector will enforce that for all 
memory cells, a cell will not be allocated in StateC iff 
it has a reference-count of 0 in StateB. NO TRANS CLOSURE
*/
fact B_to_C_GarbageCollected {
   	StateB.references = StateC.references
	all m : HeapCell | m not in StateC.allocated <=> ref_count[StateB, m] = 0
}

/* 10. Research questions: why isn't completeness satisfied, but soundness is? 
Add the extra facts, look at counterexamples, answer survey questions
*/
fact UnallocatedCantReference {
	all s : State | all m : HeapCell - s.allocated | no s.references[m]
}
pred fix {
	all s : State | all m : HeapCell | m not in m.^(s.references)
}
//check fixcompleteness {fix => complete} for 4 Memory

