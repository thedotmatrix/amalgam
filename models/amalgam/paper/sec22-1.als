abstract sig Target {}
abstract sig Name extends Target {}
sig Alias extends Name {}
sig Group extends Name {}
sig Addr extends Target {}

sig Book {
  entries: Name -> Target
} {
  -- No cycles
  all n: Name | n not in n.^entries

  -- Aliases cannot be empty (bug!)
  all a: Alias | some a.entries
}

fun lookup[b: Book, n: Name]: set Addr {
  n.^(b.entries) & Addr
}
 	  	
pred addEntryBug[b,b': Book,n: Name,t: Target] {
  b.entries != b'.entries
  -- disallow new aliasing that doesn't resolve
  some lookup[b,t]
  b'.entries = b.entries + (n->t)
}

run addEntryBug for 3 but exactly 2 Book
