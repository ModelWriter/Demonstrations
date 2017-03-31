open util/relation

one sig Model {
	has: set Requirement,

	requires: Requirement -> Requirement,
	refines: Requirement -> Requirement,
	contains: Requirement -> Requirement,
	partiallyRefines: Requirement -> Requirement,
	conflicts: Requirement -> Requirement,
	equals: Requirement -> Requirement
}{
	irreflexive[requires]
	antisymmetric[requires]
	transitive[requires]

	irreflexive[refines]
	antisymmetric[refines]
	transitive[refines]

	irreflexive[contains]
	antisymmetric[contains]
	transitive[contains]

	irreflexive[partiallyRefines]
	antisymmetric[partiallyRefines]
	transitive[partiallyRefines]

	irreflexive[conflicts]
	symmetric[conflicts]

	reflexive[equals, Requirement]
	symmetric[equals]
	transitive[equals]


	no requires & refines
	no requires & contains
	no requires & partiallyRefines
	no requires & conflicts
	no requires & equals

	no refines & contains
	no refines & partiallyRefines
	no refines & conflicts
	no refines & equals

	no contains & partiallyRefines
	no contains & conflicts
	no contains & equals

	no partiallyRefines & conflicts
	no partiallyRefines & equals

	no conflicts & equals

	no requires & ~refines
	no requires & ~contains
	no requires & ~partiallyRefines
	no requires & ~conflicts
	no requires & ~equals

	no refines & ~contains
	no refines & ~partiallyRefines
	no refines & ~conflicts
	no refines & ~equals

	no contains & ~partiallyRefines
	no contains & ~conflicts
	no contains & ~equals

	no partiallyRefines & ~conflicts
	no partiallyRefines & ~equals

	no conflicts & ~equals
}

sig Requirement {

}

fact all_reqs_in_model {
	Requirement = Model.has
}

fact equals_facts{
	all a,b: Model.has {
		b in a.(Model.equals) => a.(Model.conflicts) = b.(Model.conflicts)
		b in a.(Model.equals) => a.(Model.requires) = b.(Model.requires)
		b in a.(Model.equals) => a.(Model.equals) = b.(Model.equals)
		b in a.(Model.equals) => a.(Model.refines) = b.(Model.refines)
		b in a.(Model.equals) => a.(Model.partiallyRefines) = b.(Model.partiallyRefines)
		b in a.(Model.equals) => a.(Model.contains) = b.(Model.contains)

		b in a.(Model.equals) => a.~(Model.conflicts) = b.~(Model.conflicts)
		b in a.(Model.equals) => a.~(Model.requires) = b.~(Model.requires)
		b in a.(Model.equals) => a.~(Model.equals) = b.~(Model.equals)
		b in a.(Model.equals) => a.~(Model.refines) = b.~(Model.refines)
		b in a.(Model.equals) => a.~(Model.partiallyRefines) = b.~(Model.partiallyRefines)
		b in a.(Model.equals) => a.~(Model.contains) = b.~(Model.contains)
	}
}

fact req_ref_fact{
	all a,b,c: Model.has {
		b in a.(Model.requires) && c in b.(Model.refines) => c in a.(Model.requires)
		b in a.(Model.refines) && c in b.(Model.requires) => c in a.(Model.requires)
	}
}

fact ref_con_fact {
	all a,b,c: Model.has {
		b in a.(Model.refines) && c in b.(Model.contains) => c in a.(Model.refines)
		b in a.(Model.partiallyRefines) && c in b.(Model.contains) => c in a.(Model.partiallyRefines)
		b in a.(Model.refines) && c in b.(Model.partiallyRefines) => c in a.(Model.partiallyRefines)
		b in a.(Model.partiallyRefines) && c in b.(Model.refines) => c in a.(Model.partiallyRefines)
	}
}

run { } for exactly 3 Requirement


