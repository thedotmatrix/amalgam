abstract sig Player {}
one sig X extends Player {}
one sig O extends Player {}

abstract sig Index {}
one sig One extends Index {}
one sig Two extends Index {}
one sig Three extends Index {}

sig Board {
  turn: Player,
  places: Index -> Index -> Player
}

pred move[b: Board, r: Index, c: Index, b': Board] {
  no b.places[r][c]
  b'.turn != b.turn
  b'.places = b.places + (r->c->b.turn)
}

pred moveBuggy[b: Board, r: Index, c: Index, b': Board] {
  no b.places[r][c]
  b'.turn != b.turn
  b'.places = b.places ++ (r->c->b.turn)
}

run moveBuggy for 3 but 2 Board
run move for 3 but 2 Board
