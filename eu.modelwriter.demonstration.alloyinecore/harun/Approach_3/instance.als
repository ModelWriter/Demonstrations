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

pred remove_example {
	RequirementsModel/remove[SR12 -> SR14]
}

pred add_example {
	RequirementsModel/addPartiallyRefines[SR13 -> SR14]
}

pred transform_example {
	RequirementsModel/transformToRequires[SR12 -> SR14]
}

run remove_example

run add_example

run transform_example
