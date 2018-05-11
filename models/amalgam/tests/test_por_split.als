sig Node {edges: set Node }

-- single provenance: a->b in edges fails
--   expect a forked path because have to try instantiating a with all existing nodes
--   diff. eval. disregards skolem constants, so either direction works:
--   suppose asking @why 0->1 in edges? 
--   if a=0,b=1 derive via a->b in edges; if a=1;b=0 derive via b->a in edges
pred testSplit1 {
  some a, b: Node | {
    a != b
    a->b in edges 
    b->a in edges
  }
}
run testSplit1 for 4


-- should be split into 2 distinct provenances
--   one shows a->b in edges failing
--   another shows b->a in ~edges failing
--     ISSUE: the 2 provenances are indistinguishable. why are we never highlighting the 2 lines?
pred testSplit2 {
  some a, b: Node | {
    a != b
    a->b in edges 
    b->a in ~edges
  }
}
run testSplit2 for 4
