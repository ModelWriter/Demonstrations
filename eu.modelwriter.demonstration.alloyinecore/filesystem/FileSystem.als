--open named [Object]

sig Name{}

abstract sig Object {
	name: Name
}

sig File extends Object {
	
}

sig Dir extends Object {
	content: set Object
}

one sig Root extends Dir {

}

fact { all d: Dir | not (d in d.^content)}
fact {Object in Root.*content }
fact {all o: Object - Root | one o.~content}

fact {all disj a, b: Object - Root | a.~content = b.~content => a.name != b.name}

run {} for exactly 2 Dir , exactly 3 File, 4 Name
