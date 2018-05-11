sig A {
  rel: set A
}

sig B {}

fact {
  (rel in ~rel) implies some B
}

run {} for 1
run {} for 2
run {} for 3
run {} for 4
run {} for 5
run {} for 6
run {} for 7
