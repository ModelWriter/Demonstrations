module MAS

sig Name{}
sig Time {}

some sig SWO {
	name: one Name,
	contains:set SWO,
	has:some Role,
	interacts_with: one Environment
}

sig Environment{
	name: one Name
	//has: set Service
}

some sig SWA {
	disj name, description, properties, agent_type,	agent_state: one Name,
	//plays: Role -> Time,
	works_in: SWO one->Time,
	//applies: some Plan,
	//includes: Capability,
	cooperates: some SWA
}

sig Role {
	name:one Name
	//has: Goal 	
}

pred irreflexive[r : univ -> univ] {
	no (iden & r)
}

pred asymmetric[r : univ -> univ] {
	no (r & ~r)
}

//pred nontransitive [relation: univ -> univ]{
//  relation = ^relation
//}

pred acyclic [r: univ->univ]{
	no (^r & iden)
}

fact selfContainment{
    irreflexive[contains] && irreflexive[cooperates] && 
    asymmetric[contains] && acyclic[contains]
    // nontransitive[contains]
}

// fact {}

// fact {no (SWO<: iden & contains)}

fact MASInit{ #SWA>=2 }

pred show {}

run show for 5