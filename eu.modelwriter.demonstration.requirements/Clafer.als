module ferhat/Clafer

abstract sig Element {}
sig string extends Element {}
abstract sig boolean extends Element {}
one sig false,true extends boolean {}
--sig integer extends Element {}

/* Target: Clafer Metamodel*/
abstract sig CElement extends Element {}
sig Clafer extends CElement { 
	isAbstract: lone boolean, -- 'abstract'
	name: lone string, -- clafer's name
	cElements: set Clafer, -- subclafers
	cSuper: lone Clafer, -- superclafer ':'  -- abstract <clafer> : <superclafer>
	cTarget: lone Clafer,
	--
	cCardinality: lone (CardInterval + CCardinality), //| ? |+ | * |  Interval
	cGroupCardinality: lone (GCardInterval + GroupCardinality), //| xor |  or | mux |  opt | Interval
}
fact {
	all c, c': Clafer |  {
		c' in c.cElements => one c'.name -- All Clafers except ClaferModel has a name	
		c' in c.cElements => one c'.cCardinality and one c'.cGroupCardinality  --All Clafers except ClaferModel has Card and GCard	
	}
}

one sig ClaferModel extends Clafer { }
fact {
	all m: ClaferModel | no m.cSuper --ClaferModel has no cSuperClafer
	all m: ClaferModel | no m.cTarget --ClaferModel is not a reference Clafer
	all m: ClaferModel, c: Clafer | m != c.cSuper --ClaferModel cannot be a super Clafer
	all m: ClaferModel | no m.name -- ClaferModel has no name
	all m: ClaferModel | no m.isAbstract -- ClaferModel has no isAbstract
	all m: ClaferModel | no m.cCardinality -- ClaferModel has no Card
	all m: ClaferModel | no m.cGroupCardinality -- ClaferModel has no Card
}

fact {
	no c: Clafer | c in c.^cElements --no Clafer cycles exist
	no c: Clafer | c in c.^cSuper -- no superClafer cycles exist
	Clafer in ClaferModel.*cElements --each Clafer is reachable from the ClaferModel
	all c: Clafer | lone c.~cElements --each Clafer has at most one parent
	no disj c, c': Clafer, c'': Clafer | c in c''.cElements and c' in c''.cElements and some c.name & c'.name --no overlapping Clafer names in the same level, 
	all c: Clafer | c in ClaferModel.cElements => one c.isAbstract --abstract clafers are shown only in Top Level
	all c: Clafer | c !in ClaferModel.cElements => no c.isAbstract --inner Clafers cannot be defined as abstract	
	all c, c': Clafer, m: ClaferModel |  c.cSuper = c' => c' in m.cElements and c'.isAbstract = true -- only super typing to top level 'abstract' Clafers
	all c, c': Clafer, m: ClaferModel |  c.cTarget = c' => c' in m.cElements --only reference to top level Clafers
	all c: Clafer, m: ClaferModel |  c in m.cElements => no c.cTarget -- Top Level Clafer can not be a reference clafer
	no c: Clafer | one c.cTarget and one c.cSuper --a clafer cannot be a reference clafer and has super type at the same time
}

abstract sig CInterval extends CElement { min, max : Int }
fact { 
	all i:CInterval | {
		i.min >= 0
		i.max >= i.min || i.max = -1
		i.min = 0 => i.max != 0 or i.max = 1 or i.max = -1
		i.min = 1 => i.max = -1 or i.max >= 1 } }

abstract sig CCardinality extends CElement {}
lone sig CardLone extends CCardinality {} //? : 0..1
lone sig CardSome extends CCardinality {} //+ : 1..*
lone sig CardAny extends CCardinality {} //* : 0..*
lone sig CardEmpty extends CCardinality {} // 1..1
sig CardInterval extends CInterval {} // int .. int

abstract sig GroupCardinality extends CElement {}
lone sig GCardMux extends GroupCardinality {} //mux: 0..1
lone sig GCardOr extends GroupCardinality {} //or: 1..*
lone sig GCardOpt extends GroupCardinality {} //opt: 0..*
lone sig GCardXor extends GroupCardinality {} //xor: 1..1
sig GCardInterval extends CInterval {} // int .. int

fact realismConstraint {some Clafer}

//fact { all i:CInterval, c: Clafer | i in c.cCardinality or i in c.cGroupCardinality} -- implicit containment without an explicit relation

/* Helper Predicates*/
pred acyclic [s: set univ, r: univ->univ] { no x: s | x in x.^r }

/* Counterexample Finding */
assert noMoreThanOneTopLevelClafer {#ClaferModel.cElements > 2}
check noMoreThanOneTopLevelClafer for 10 Element

assert noSubClaferExist { some c, c': Clafer | c in c'.cElements }
check noSubClaferExist for 15 Element

pred example { #Clafer > 3 and #cTarget> 1 and #cSuper> 1 and #CardInterval>0 }
run example for 20 Element
