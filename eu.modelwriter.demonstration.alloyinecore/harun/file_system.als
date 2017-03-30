abstract sig Object {
	name: one Name
}

sig File extends Object {

}

sig Folder extends Object {
	contents: set Object
}

sig Shortcut extends File {
	targets: one Object
}

sig Name {
	
}

one sig Root extends Folder {

}

fact { all o,p:Object | (o != p && o.~contents = p.~contents) => o.name != p.name }
fact { all n:Name | some n.~name }
fact { all o:Object | lone o.~contents }
fact { all s:Shortcut | s.targets !in Shortcut }
fact { all r:Root | no r.~contents }
fact { all f:Object - Root | one f.~contents }
fact { all f:Folder | f !in f.contents}
fact { all o:Object - Root | Root in o.^~contents }

run { } for 5
