module OntologyVP
open util/time

sig Name{}
abstract sig Type {}
one sig Dynamic, Static extends Type{}


sig RoleOntology extends ODMOWLOntology{
}

sig OrganizationOntology extends ODMOWLOntology{
}

sig ServiceOntology extends ODMOWLOntology{
}

sig Role {
	name:one Name,
	//has: Goal some-> one Time,
	//interacts_with: some SWS,
	//realizes: some Interaction,
	knowsRoleOntology: some RoleOntology,
	knowsOrganizationOntology: some OrganizationOntology 
}

sig ArchitectureRole extends Role{
}

sig OntologyMediatorRole extends ArchitectureRole{
	knows: some ServiceOntology
}

sig SWS{
	name: one Name,
	//composed_of: some WebService,
	depends_on: some ServiceOntology
}

sig SWO {
	//name: one Name,
	//contains: SWO,
	has:some Role,
	//interacts_with: one Environment
	knowsOrganizationOntology: some OrganizationOntology
}

sig ODMOWLOntology{
	name: one Name,
	description:one Name,
	includesStatement: some ODMOWLStatement,
	includesClass: ODMOWLClass
}
sig ODMOWLStatement{
	name: one Name,
	subject: one Name,
	predicate: one Name,
	object: one Name
}
 sig ODMOWLClass{
	name: one Name
}

sig Fact extends ODMOWLStatement{

}

sig Belief extends ODMOWLStatement{
	//disj name, description: one Name, dynamic: one Bool,
	description: one Name,
	update_type:one Type
   //precondition:Goal->one Event,
}
sig SWA {
	plays: Role one-> Time

}


fact OntologyDependency{
	all swo:SWO, r:Role | some OrgOnt: OrganizationOntology| swo.knowsOrganizationOntology = OrgOnt && 
	r.knowsOrganizationOntology = OrgOnt => swo.has = r	
}

pred show{
}
pred BarterOntologies(BarterManager: SWA, 
BarterOntology: RoleOntology, 
BMW520Tyre: ODMOWLClass, BarterRole:Role, BarterOrgOntology: OrganizationOntology,
GlobalInsurance:ODMOWLClass){
	some t:Time | BarterOntology.includesClass=BMW520Tyre 
	&& BarterRole.knowsRoleOntology = BarterOntology 
	&& BarterManager.plays.t = BarterRole && BarterRole.knowsOrganizationOntology=BarterOrgOntology
  && BarterOrgOntology.includesClass= GlobalInsurance
}


//run show
run BarterOntologies
