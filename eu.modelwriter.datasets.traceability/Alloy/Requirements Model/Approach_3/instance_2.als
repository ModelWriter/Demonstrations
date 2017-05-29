open requirements_model[Requirement] as RequirementsModel

abstract sig Requirement {}

one sig r1 extends Requirement {}
one sig r2 extends Requirement {}
one sig r3 extends Requirement{}
one sig r4 extends Requirement {}
one sig r5 extends Requirement {}
one sig r6 extends Requirement {}
one sig r7 extends Requirement {}
one sig r8 extends Requirement {}
one sig r9 extends Requirement {}
one sig r10 extends Requirement {}
one sig r11 extends Requirement {}
one sig r12 extends Requirement {}
one sig r13 extends Requirement {}
one sig r14 extends Requirement {}
one sig r15 extends Requirement {}
one sig r16 extends Requirement {}

fact init_req_model {
	RequirementsModel/Requires[r13 -> r16 + r11 -> (r14 + r15) + r10 -> (r12 + r13 + r14) + r15 -> r16 + r14 -> r16 + r7 -> (r8 + r9) + r3 -> r9 + r5 -> r9]
	RequirementsModel/Contains[r1 -> (r2 + r5 + r3 + r6 + r4 + r7) + r9 -> (r10 + r11)]
	RequirementsModel/NoEquals
	RequirementsModel/NoRefines
	RequirementsModel/NoPartiallyRefines
	RequirementsModel/NoConflicts
}

pred remove_example {
}

pred add_example {
	addRefines[r6->r8]
}

pred transform_example {
}

run remove_example

run add_example

run transform_example
