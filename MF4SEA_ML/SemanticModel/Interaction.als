module Interaction
open util/ordering[Time] 

sig Name{}
sig Time{}

sig SWA{
	cooperates: some SWA
}

sig Interaction extends FIPAContractNet{
	name: one Name,
	has: one MessageSequence,
	includes: some Message	
}

sig Message{
	content, content_language, message_type, performative: one Name,
	sender:one SWA,
	receiver: some SWA,
	sentTime:Time
}

sig MessageSequence {
	id: one Int,
	agent_set: some SWA  
}

sig FIPAContractNet{
	spec_no: one Int
}

pred irreflexive[relation : univ -> univ] {
	no (iden & relation)
}

fact irreflexiveAndAsymmetric{
	irreflexive[cooperates] 
}

fact AgentTalking{
	all m: Message| some swa1,swa2: SWA| swa1 in m.receiver && swa2 in m.sender=>
	swa2 in swa1.cooperates || swa1 in swa2.cooperates
}

fact AgentSet{
	all i:Interaction | some m:Message, ms: MessageSequence| 
	m in  i.includes && ms in i.has &&
 	m.receiver in ms.agent_set && m.sender in ms.agent_set 
}

fact SelfMessaging{
	all m:Message| m.sender != m.receiver     
}

pred ReceiveMsg (swa:SWA, t:Time, msg: Message){
	MsgReceivePrecondition [swa, msg, t]
	let t' = prev[t] {
		let getMessage = SWA->Time->Message{
			swa.getMessage[t] = swa.getMessage[t'] + msg
		}	
	}
 	msg.receiver= SWA 
}
pred MsgReceivePrecondition (swa: SWA, msg:Message, t:Time){
	let getMessage = SWA->Time->Message{ 
		msg !in swa.getMessage[prev[t]] 
		msg.sentTime in prevs[t]	
	}
}

pred SendMsg (swa:SWA, t:Time, msg: Message){
	let t' = prev[t] {
		let sendMessage = SWA->Time->Message{
			swa.sendMessage[t] = swa.sendMessage[t'] + msg
		}	
	}
	msg.sender = SWA && msg.sentTime =t 
}

pred show {}

run show 
