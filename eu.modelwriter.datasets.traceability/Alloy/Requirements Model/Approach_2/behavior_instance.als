open requirements_model[Requirement] as RequirementsModel

abstract sig Requirement {}

one sig SR9 extends Requirement {}
one sig SR10 extends Requirement {}
one sig SR11 extends Requirement{}
one sig SR12 extends Requirement {}
one sig SR13 extends Requirement {}
one sig SR14 extends Requirement {}

fact init_req_model {
	RequirementsModel/Requires[(SR13 + SR14) -> SR10 + SR14 -> SR11]
	RequirementsModel/Contains[SR9 -> (SR10 + SR11)]
	RequirementsModel/Equals[SR12 -> SR14]
	RequirementsModel/NoRefines
	RequirementsModel/NoPartiallyRefines
	RequirementsModel/NoConflicts
}



one sig ModifiedModel extends RequirementsModel/RequirementsModel {
	impact: Requirement -> Requirement
}

pred remove[rm, rm': RequirementsModel/RequirementsModel, r: Requirement] {
	rm'.impact = r<:rm.(requires + contains + equals + refines + partiallyRefines + conflicts) + rm.(requires + contains + equals + refines + partiallyRefines + conflicts):>r
	rm'.requires = rm.requires - rm'.impact
	rm'.contains = rm.contains - rm'.impact
	rm'.equals = rm.equals - rm'.impact
	rm'.refines = rm.refines - rm'.impact
	rm'.partiallyRefines = rm.partiallyRefines - rm'.impact
	rm'.conflicts = rm.conflicts - rm'.impact
}

pred init {
	remove[RequirementsModel/InferredModel, ModifiedModel, SR14]
}

run init
