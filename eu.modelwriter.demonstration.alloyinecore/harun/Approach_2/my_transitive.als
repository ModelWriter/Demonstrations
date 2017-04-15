open util/relation

abstract sig R {
	contains: set R
} 

one sig R1, R2, R3, R4 extends R{}

fact {
	all r, r', r'': R | r' in r.contains and r'' in r'.contains implies r'' in r.contains
}

check {
	transitive[contains]
} 

run { R1 -> R2 + R2->R3 + R3 -> R4  in contains and irreflexive[contains] }
