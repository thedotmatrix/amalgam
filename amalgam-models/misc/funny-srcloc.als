/*
Top level let could introduce a weird srcloc. Consider this specification
and asking why not Alias$0 -> something (say, Group$0). The alpha for

Alias$0 -> Group$0 in this/Alias -> this/Addr + this/Name

spans from the first line to the inner let expression
*/

let Target = Addr + Name
abstract sig Name {
    address: set Target
}
sig Alias, Group extends Name {}
sig Addr {}

fact {
	no ^address & iden
	(^address & (Name -> Addr)).Addr = Name

	let aliasLink = (Alias -> Target) & address | {
		~aliasLink.aliasLink in iden
	}
}

run {} for 1
run {} for 2
run {} for 3
run {} for 4
run {} for 5
