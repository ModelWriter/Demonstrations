module Environment

open util/boolean
open util/time

sig Name{}

some sig SWA {
	disj name,description,property,agent_type,agent_state:one Name,
	access_to:  some Environment,
	works_in: SWO one->Time
}

sig Environment{
	name: one Name,
	hasFact: set Fact,
	hasService: set Service,	
	hasResource: set Resource	
}

sig Service{
	name: one Name
}

sig Fact {
	name: one Name, 
	subject: one Name,
	predicate: one Name,
	object: one Name
}

sig Resource{
	name:one Name,
	IsSharable: Bool
}

sig SWO{
	interacts_with: one Environment
}

fact EnvironmentComposition{
	all s:Service, f:Fact, r:Resource| 
	s.~hasService != none && 
	f.~hasFact !=none && 
	r.~hasResource ! = none 
}

fact EnvAccess{
	all swa: SWA | some t:Time, swo: SWO | 
	swa.works_in.t = swo &&
	swa.access_to in swo.interacts_with
}

fact ResourceAcccess{
	let  access = access_to.hasResource ->Time {
		all a1,a2:SWA| a1.access=a2.access => a1=a2
	} 	
}

pred show{}
run show
