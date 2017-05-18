--Default Top Root Set, corresponds to Java Object
sig Object {}

--class Name {}
sig Name in Object{}

-- abstract class FSObject {}
sig FSObject in Object { name: Name}

 -- class File extends FSObject, Executable {}
sig File in FSObject + Executable { }

-- abstract class Executable {}
sig Executable in Object { depend : set File } 

-- class Link  extends FSObject {}
sig Link in FSObject { link: one FSObject }

-- class Dir  extends FSObject {}
sig Dir in FSObject { content: set FSObject}

-- class Root  extends Dir {}
sig Root in Dir{ }

--Auto-generated (default)
fact NoStrayObjects{ Object = FSObject + Executable + Name}

--Auto-generated
fact Inheritance{
	-- class File, Dir, Link extends FSObject {},  -- abstract class FSObject {}
	FSObject = File + Dir + Link --because FSObject is abstract
    no File & Dir and no (File + Dir) & Link --	no File & Dir and no Dir & Link and no File & Link  --(exponential rewriting)
	/* no File & Dir and no (File + Dir) & Link and no (File + Dir + Link) & X   --(linear rewriting) */

	-- Detect Unconnected Components in Inheritance Graph and Generate this rule
	no Name & (FSObject + Executable)

	-- abstract class Executable {}, class File extends FSObject, Executable {}
	no Executable - File	--Because of abstract keyword
}

--Auto-generated
fact Composition{
	all o: FSObject  | lone o.~content
	FSObject in Dir.*content
}

--User's facts
fact {one Root }
fact {no Root.~content}
fact {all e: Executable | not (e in e.^depend) }
fact {all d: Dir | not (d in d.^content)}
fact { all l: Link | not (l in l.^link) }
fact {FSObject in Root.*content }
fact {all disj a, b: FSObject - Root | a.~content = b.~content => a.name != b.name}

run {#Executable > 0 and #depend= 2 and File != Executable and #link > 0 and #Dir>3} for exactly 11 Object
