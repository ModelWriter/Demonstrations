open requirements_model[O] as RequirementsModel

abstract sig O {}
one sig A, B, C, D, E extends O {}

fact {
	RequirementsModel/Requires[A -> B + C -> D]
	RequirementsModel/Refines[B -> C]
	RequirementsModel/NoPartiallyRefines
	RequirementsModel/NoConflicts
	RequirementsModel/NoContains
	RequirementsModel/NoEquals
}

run {}
