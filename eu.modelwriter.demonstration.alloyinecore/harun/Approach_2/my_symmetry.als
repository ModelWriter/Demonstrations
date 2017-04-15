open util/relation

sig R {
	conflicts: set R
} 

fact {
	all r, r': R | r' in r.conflicts => r in r'.conflicts
}

check {
	symmetric[conflicts]
} for 5 R

run { some conflicts } for 5 R
