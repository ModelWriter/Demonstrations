module Plan

open util/ordering[Plan] as plan
open util/ordering[Task] as task
open util/ordering[Action] as action

sig Name{}

sig SWA {}

sig Plan {
	disj name, type, description: one Name, 
	priority: one Int,
	composed_of: set Task
}

sig Task{
	id: one Int,
	composed_of: set Action,
}

sig Action{
	id: one Int
}

sig Send extends Action{
	send: one Message
}

sig Receive extends Action{
	receive: one Message
}

sig Message{
	content, content_language, message_type, performative: one Name,
	sender: one SWA,
	receiver: some SWA
}

sig Role {
	has: set Goal,
	realizes: some Interaction
}

sig Goal {
	realized_by: set Plan
}

sig Interaction {
	includes: set Message
}

fact ActionTaskOrdering{
  all disj T1,T2: Task| T1.id<=T2.id => task/next [T1] =T2
  all disj A1,A2: Action| A1.id<=A2.id =>action/next[A1]=A2
}

fact PlanInternal{
	all t:Task, a:Action| 
	t.~composed_of != none && 
	a.~composed_of !=none 
}

fact MessageAccess{
	some r1:Role, g:Goal, t:Task, s:Send, r:Receive, i:Interaction, p:Plan| all m:Message | 
	r1.has = g &&g.realized_by =p && p.composed_of=t && 
	{t.composed_of= r || t.composed_of = s}&&
	{s.send= m || r.receive=m} => r1.realizes=i && i.includes=m
}

fact PlanPriority{
	all p1, p2:Plan| p1.priority<p2.priority => plan/prev[p2]=p1
}

fact MessageFact{
	all m:Message| some s:Send, r:Receive | m.~send=s|| m.~receive=r
}

pred show{}

run show for 8
