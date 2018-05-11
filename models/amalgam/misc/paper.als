abstract sig Target {}
abstract sig Name extends Target {}
sig Alias extends Name {}
sig Group extends Name {}
sig Addr extends Target {}

one sig Book {
  entries: Name -> Target
} {
  -- No cycles
  all n: Name | n not in n.^entries

  -- Aliases cannot be empty (bug!)
  all a: Name | some a.entries
}
run {}
