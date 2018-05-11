sig Player {}
sig Index {}
sig Board {
  turn: Player,
  places: Index -> Player
}

pred moveBuggy[b: Board, r: Index, b': Board] {
  //no b.places[r]
  //b'.turn != b.turn
  b'.places = b.places + (r->b.turn)
}

run moveBuggy for exactly 2 Board, exactly 2 Player, exactly 2 Index
