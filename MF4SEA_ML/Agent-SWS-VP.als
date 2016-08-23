// some of the relations such as name for main elements and some the elements such IOPE are omitted to make the model simpler.

// Time and Order relations are omitted and replaced with subset relation to omit the 3rd arity in the relations 

module MF4SEA_ML

// sig Name{}

sig SWA {
	// disj name, description, property, agent_type, agent_state : one Name,
	plays: Role,
	applies: some Plan,
	// from MAS&Org vp
	cooperates: some SWA	
}

sig SS_MatchmakerAgent extends SWA{
	appliesSS_RegisterPlan : some SS_RegisterPlan,
	playsRegistrationRole: RegistrationRole
}

sig Role {
	// name: one Name,
	interacts_with: some SWS
}

sig RegistrationRole extends Role{
	advertises: some SWS
}

sig SWS{
	// name: one Name,
	composed_of: some WebService
}

sig Interface{
	// name: one Name,
	presents: some SWS
}

sig Process {
	described_by: some SWS
}

sig Grounding{
	supports: some SWS,
	calls: some WebService 
}

sig Service{
	// name: one Name
}

sig WebService extends Service{
}

sig Plan {
	// disj name, type, description: one Name,
	// priority: one Int
}

sig SS_RegisterPlan extends Plan{
	advertises: some Interface
}

sig SS_FinderPlan extends Plan {
	interacts_with: some SS_MatchmakerAgent,
	discovers: set Interface
}
sig SS_AgreementPlan extends Plan{
	negotiates: some Interface
}

sig SS_ExecutorPlan extends Plan{
	executes: some Process,
	uses: some Grounding
}

sig Environment{
	// name: one Name,
	hasService: set Service
}

///////////    FACTS    //////////////////////

fact ServiceComposition{
	all s:Service | s.~hasService != none
	all wb:WebService | wb.~composed_of != none
}

fact Agent_SWS_Interaction{
	all e: Environment | some ws:WebService |
	ws in e.hasService => {some swa1, swa2:SWA, sws1,sws2:SWS, r:Role, f:SS_FinderPlan, i:Interface, x:Int | 
		r in swa1.plays && sws1 in r.interacts_with && f in swa2.applies && i in f.discovers &&
		i.presents= sws2 && #sws1 =x && x.plus[#sws2] >=1 }
}

fact InheritanceBreak {
	no a:SWA, rp:SS_RegisterPlan | rp in a.applies
}

fact InterfaceControl{
  all f:SS_FinderPlan, r:SS_RegisterPlan, a:SS_AgreementPlan |
    f.discovers in r.advertises && a.negotiates in f.discovers 
  all i:Interface, p:Process, g:Grounding, e:SS_ExecutorPlan |
	p in e.executes && g in e.uses && p.described_by in i.presents && g.supports in i.presents 
}

// fact PlanStates{ 
//	 all disj f:SS_FinderPlan | some r:SS_RegisterPlan |
//		 prevs[f]= r
//	 all a:SS_AgreementPlan | some f:SS_FinderPlan |
//		 prevs[a] = f
//	 all e:SS_ExecutorPlan |some a:SS_AgreementPlan |
//		 prevs[e]=a 
// }

//fact SWSInteractionProcedure { 
//	all a: SWA, ma:SS_MatchmakerAgent, rp:SS_RegisterPlan,
//	fp:SS_FinderPlan, ap:SS_AgreementPlan,ep:SS_ExecutorPlan,
//	i:Interface, p:Process, g:Grounding,ws:WebService | some
//	t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11: Time | 
//		ma.appliesSS_RegisterPlan[rp]=t1 &&
//		rp.advertises[i] = t2 && prev[t2]=t1 &&
//		(a.applies[fp] = t3&& prevs[t3]=t2 && fp.interacts_with[ma]=t4 && 
//		fp.discovers[i]=t5 && prev[t5] = t4 && prev[t4]=t3) && 
//		(a.applies[ap] = t6 && ap.negotiates[i]=t7 && 
//		(fp.finding_result = True =>
//		(next[t5]=t6 && next[t6]= t7) else
//		(t6=none && t7= none)))&&(a.applies[ep] = t8 &&
//		ep.executes[p]=t9 && (ap.agreement_result!=True =>
//		(t8=none && t9= none) else (next[t7]=t8 && next[t8]=t9 &&
//		(ep.uses[g] = t10&& g.calls[ws] =t11 &&
//		(next[t9] = t10 && next[t10] = t11)))))
//}

fact Agent_SWSPlanOrdering {
	all swa:SWA, sm:SS_MatchmakerAgent |
		(SS_FinderPlan in swa.applies => #(sm.appliesSS_RegisterPlan) >=1) &&
		(SS_AgreementPlan in swa.applies => SS_FinderPlan in swa.applies) &&
		(SS_ExecutorPlan in swa.applies => SS_AgreementPlan in swa.applies)
}

// from MAS&Org vp
fact MASInýt{
	#SWA>=2
}

pred irreflexive[r: univ -> univ] {
	no (iden & r)
}

// pred asymmetric[r: univ -> univ] {
//		no (r & ~r)
// }

// pred acyclic [r: univ->univ]{
//		no (^r & iden)
// } 

fact selfContainment { 
	irreflexive[cooperates] 
	// irreflexive[contains] && asymmetric[contains] && acyclic[contains]  // relation with SWO
}

// from Role vp
fact RoleModularity {
	all r:Role | r.~plays!= none // || r.~has!= none   // for relation with SWO in MAS&Org vp  
}

//////////////  Assertions   ///////////////////

assert PlanTypeProperty {
	all fp: SS_FinderPlan, ap:SS_AgreementPlan, ep:SS_ExecutorPlan |
		#ap >= 1 => #fp >=1 && 
		#ep >= 1 => #ap >=1
}

assert RegistrationProperty {
	all swa:SWA, sm:SS_MatchmakerAgent |
		swa.applies !=none => sm.appliesSS_RegisterPlan ! = none
}

assert NoConflictProperty {
	no ma:SS_MatchmakerAgent | some rp:SS_RegisterPlan | 
		ma.applies= rp
}

assert EnvironmentProperty{
	no ws:WebService |
		#ws.~hasService = 0
}

/////////////  Predicates    ///////////////////////

pred show{}

pred Initialize {
	one appliesSS_RegisterPlan
}

pred SWAstart { 
	some SWA && one SS_MatchmakerAgent && one SS_FinderPlan && 
	SS_MatchmakerAgent.applies = none
}

////////////     Commands     //////////////////////

run show

// check RegistrationProperty