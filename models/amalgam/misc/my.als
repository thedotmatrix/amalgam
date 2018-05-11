abstract sig Player {}
one sig X extends Player {}
one sig O extends Player {}

sig Index {}

sig Board {
  turn: Player,
  places: Index -> Player
}

pred moveBuggy[b: Board, r: Index, b': Board] {
  no b.places[r]
  b'.turn != b.turn
  b'.places = b.places ++ (r->b.turn)
}

run {
  some b, b' : Board | some r : Index |
    moveBuggy[b, r, b']
} for 3 but 2 Board, exactly 3 Index
