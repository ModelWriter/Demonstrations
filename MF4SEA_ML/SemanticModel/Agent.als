open util/time
open  util/boolean

sig Name{}

sig Event{}

some sig SWA {
    disj name,description,property,agent_type,agent_state:one Name,
	plays: Role -> Time,
	includes: Capability
}

abstract sig Type {}

one sig Dynamic, Static extends Type{}

sig Role {
	name:one Name,
	has: Goal 	
}

sig Goal{
	disj name, description: one Name, 
	retry: one Bool,
	postcondition:set Belief-> one Event,
	realized_by:some Plan
}

sig Belief {
	disj name, description: one Name, 
	update_type:one Type ,
	precondition: set Goal->one Event
}

sig Plan {
	disj name, type, description: one Name, priority: one Int,
}

sig Capability {
	disj name:one Name, priority: one Int,
	appliesPlan:some Plan,
	includesBelief:set Belief,
	usesGoal:set Goal
}

fact CapabilityCoverage {	   
	all g:Goal|some p:Plan|
	g.realized_by = p && p.~appliesPlan = g.~usesGoal
	all b:Belief,g:Goal|some c:Capability,e:Event|c.usesGoal=g  
	&& g.postcondition.e=b  => b in c.includesBelief 
}

fact CapabilityComposition{ 
	all p:Plan, b:Belief|
	p.~appliesPlan!=none && b.~includesBelief ! = none 
}

fact BeliefNonSharablity{
	no b:Belief|some disj swa1,swa2:SWA|some 
	c:Capability| c.includesBelief=b && 
	(swa1.includes=c&&swa2.includes=c)
}

assert CapabilityProperty{
	all disj c1,c2: Capability| no p:Plan, g:Goal| g.realized_by=p &&p.~appliesPlan=c1 && g.~usesGoal=c2
}

//check CapabilityProperty for 30

pred show{}

run show for 5