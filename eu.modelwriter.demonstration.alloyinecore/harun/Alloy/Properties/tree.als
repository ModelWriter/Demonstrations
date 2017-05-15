
open util/relation

sig Element {
	depend: set Element,
	mandatory: set depend
}

one sig Root in Element {}

fact {
	partialOrder[depend, Element]
	irreflexive[mandatory]
}

pred aa {
	all f: Element - Root | f in Root.depend
}

run aa for exactly 4 Element 
