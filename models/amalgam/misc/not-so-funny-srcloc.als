abstract sig Name {
    address: set (Addr + Name)
}
sig Alias, Group extends Name {}
sig Addr {}

fact {
	no ^address & iden
	(^address & (Name -> Addr)).Addr = Name

	let aliasLink = (Alias -> (Addr + Name)) & address | {
		~aliasLink.aliasLink in iden
	}
}

run {} for 1
run {} for 2
run {} for 3
run {} for 4
run {} for 5
