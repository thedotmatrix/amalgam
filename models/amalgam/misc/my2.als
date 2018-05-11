abstract sig Player {}
one sig X extends Player {}
one sig O extends Player {}

sig Index {}

sig Board {
  turn: Player,
  places: Index -> Index -> Player
}

pred moveBuggy[b: Board, r: Index, c: Index, b': Board] {
  no b.places[r][c]
  b'.turn != b.turn
  b'.places = b.places ++ (r->c->b.turn)
}

run moveBuggy for 3 but 2 Board, exactly 3 Index
