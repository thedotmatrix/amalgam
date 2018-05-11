sig Cyclic { succ : Cyclic }
one sig Z extends Cyclic {}

fact {
  all x, y : Cyclic | x.succ = y.succ implies x = y
}

run { } for 4



