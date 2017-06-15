module TraceabilityModel
open util/relation

abstract sig Artifact {
	requires: set Artifact,	refines: set Artifact,
	contains: set Artifact,	conflicts: set Artifact}

-- Locate@File
sig Specification extends Artifact {}

-- Locate@Text
sig Requirement extends Artifact { equals: set Requirement}

-- Locate@Text
sig LowLevelReq, HighLevelReq extends Requirement { }

abstract sig Implementation extends Artifact {
	satisfies: set Requirement}

-- Locate@Code
sig Code extends Implementation {}

-- Locate@Model
sig Model extends Implementation {}

fact {injective[contains, Artifact]}
fact {irreflexive[requires + refines + contains + conflicts]}
fact {antisymmetric[requires + refines + contains]}

-- Reason@Artifact.conflicts
fact {all a,b,c: Artifact |
		b in a.(requires + refines + contains) and 
					c in b.conflicts => c in a.conflicts
	symmetric[conflicts]}

-- Reason@Implementation.satisfies
fact {all a,b,c : Artifact {
		b in a.refines and b in c.satisfies => 
										a in c.satisfies
		b in a.refines and c in b.satisfies => 
										c in a.satisfies }}
-- Reason@Artifact.requires
fact {all a,b,c: Artifact {
		b in a.requires and c in b.(refines + contains) and 
		   c !in a.(refines + contains) => c in a.requires
		b in a.(refines + contains) and c in b.requires and 
		   c !in a.(refines + contains) => c in a.requires}}

fact {no conflicts & 
		(requires + refines + satisfies + contains)}


