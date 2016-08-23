module Role

sig Name{}

sig SWO {
	has: set Role
}

sig SWA {
	plays: set Role
}

sig Interaction{
	name: one Name,
}

sig Role {
	name:one Name,
	realizes: some Interaction,
}

sig RegistrationRole extends ArchitectureRole{}

sig OntologyMediatorRole extends ArchitectureRole{}

sig ArchitectureRole extends Role{}

sig DomainRole extends Role{}

fact RoleModularity{
	all r:Role|  r.~has!=  none || r.~plays!=none
}

pred show{}
run show
