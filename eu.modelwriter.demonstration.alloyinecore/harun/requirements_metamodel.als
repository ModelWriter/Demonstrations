abstract sig Object {
	name: Name
}

one sig RequirementsModel extends Object {
	includes: set ModelObject
}

abstract sig ModelObject extends Object {
}{
	all o: ModelObject | one o.~includes
}

sig Requirement extends ModelObject {
	id: ID,
	description: Description,
	priority: Priority,
	reason: Reason,
	status: Status,

	source: Relationship,
	target: Relationship
}

abstract sig Relationship extends Object {} { all r:Relationship | some r.~source + r.~target }

lone sig Requires extends Relationship {}
lone sig Refines extends Relationship {}
lone sig PartiallyRefines extends Relationship {}
lone sig Conflicts extends Relationship {}
lone sig Contains extends Relationship {}
lone sig Equals extends Relationship {}

abstract sig StringR {}
abstract sig Integer {}

sig ID extends Integer {} { all i:ID | one i.~id }
sig Name extends StringR {}{ all n:Name | one n.~name }
sig Description extends StringR {} { all d:Description | one d.~description }
sig Reason extends StringR {} { all r:Reason | one r.~reason }

abstract sig Priority {}{ all p:Priority | some p.~priority }
abstract sig Status {}{ all s:Status | some s.~status }

fact { all r:Requirement | r.target!=r.source }

lone sig Proposed extends Status {}
lone sig Analyzed extends Status {}
lone sig Accepted extends Status {}
lone sig Rejected extends Status {}
lone sig Replaced extends Status {}

lone sig Neutral extends Priority {}
lone sig LowCritical extends Priority {}
lone sig Critical extends Priority {}
lone sig VeryCritical extends Priority {}

fact { all s:Status | some s.~status }
fact { all p:Priority | some p.~priority } 

run {} for exactly 2 Requirement, 9 StringR, 2 Integer, 1 Priority, 1 Status
