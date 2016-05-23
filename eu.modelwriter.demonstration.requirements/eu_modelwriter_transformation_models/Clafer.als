module eu_modelwriter_transformation_models/Clafer

open eu_modelwriter_transformation/Type
open eu_modelwriter_transformation/Helper

/* Target: Clafer Metamodel*/
abstract sig CElement extends Element {}
sig Clafer extends CElement { 
	isAbstract: lone boolean, -- 'abstract'
	name: lone string, -- clafer's name
	cElements: set Clafer, -- subclafers
	cSuper: lone Clafer, -- superclafer ':'  "abstract <clafer> : <superclafer>"
	cTarget: lone Clafer,
	cCardinality: lone CCardinality, -- "? | + | * (default) | Interval"
	cGroupCardinality: lone GroupCardinality, -- "xor |  or | mux |  opt (default) | Interval"
}
fact {
	all c, c': Clafer |  {
		-- All Clafers except ClaferModel has a name
		c' in c.cElements implies one c'.name 	
		--All Clafers except ClaferModel has Card and GCard
		c' in c.cElements implies one c'.cCardinality and one c'.cGroupCardinality 
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
	all c: Clafer | c in ClaferModel.*cElements --each Clafer is reachable from the ClaferModel
	all c: Clafer | lone c.~cElements --each Clafer has at most one parent
	--no overlapping Clafer names in the same level
	no disj c, c': Clafer, c'': Clafer | c in c''.cElements and c' in c''.cElements and some c.name & c'.name  
	all c: Clafer | c in ClaferModel.cElements => one c.isAbstract --abstract clafers are shown only in Top Level
	all c: Clafer | c !in ClaferModel.cElements => no c.isAbstract --inner Clafers cannot be defined as abstract	
	all c, c': Clafer, m: ClaferModel { 
		c.cSuper = c' => c' in m.cElements and c'.isAbstract = true -- only super typing to top level 'abstract' Clafers
		c.cTarget = c' => c' in m.cElements --only reference to top level Clafers
		c in m.cElements => no c.cTarget -- Top Level Clafer can not be a reference clafer
	}
	no c: Clafer | one c.cTarget and one c.cSuper --a clafer cannot be a reference clafer and has super type 
	-- The default multiplicity depends on the parent clafer’s group cardinality: if the group is 0..* (opt) 
	-- at the same time then the default multiplicity is 1 (empty), otherwise it is 0..1 (?)
	all c:Clafer { 
		c.cGroupCardinality in GCardEmpty implies c.cElements.cCardinality in CardOne 
			else c.cElements.cCardinality in CardLone  
		c.cGroupCardinality !in GCardEmpty implies #c.cElements > 1
	}
}

abstract sig CCardinality extends CElement {} {all c: CCardinality | some c.~cCardinality}
lone sig CardLone extends CCardinality {} //? : 0..1
lone sig CardSome extends CCardinality {} //+ : 1..*
lone sig CardAny extends CCardinality {} //* : 0..* (default)
lone sig CardOne extends CCardinality {} // 1..1
lone sig CardInterval extends CCardinality { min, max : Int } // int .. int
fact { 
	all i:CardInterval | {
		i.min >= 0
		i.max >= i.min || i.max = -1
		i.min = 0 => i.max != 0 or i.max = 1 or i.max = -1
		i.min = 1 => i.max = -1 or i.max >= 1 } }

abstract sig GroupCardinality extends CElement {} {all g: GroupCardinality | some g.~cGroupCardinality}
lone sig GCardMux extends GroupCardinality {} //mux: 0..1
lone sig GCardOr extends GroupCardinality {} //or: 1..*
lone sig GCardEmpty extends GroupCardinality {} //opt: 0..* (default)
lone sig GCardXor extends GroupCardinality {} //xor: 1..1
lone sig GCardInterval extends GroupCardinality { min, max : Int } // int .. int
fact { 
	all i:CardInterval | {
		i.min >= 0
		i.max >= i.min || i.max = -1
		i.min = 0 => i.max != 0 or i.max = 1 or i.max = -1
		i.min = 1 => i.max = -1 or i.max >= 1 } }

fact realismConstraint {some Clafer}

/* Counterexample Finding */
assert noMoreThanOneTopLevelClafer {#ClaferModel.cElements > 2}
check noMoreThanOneTopLevelClafer for 10 Element

assert noSubClaferExist { some c, c': Clafer | c in c'.cElements }
check noSubClaferExist for 15 Element

pred example { #Clafer > 3 and #cTarget> 1 and #cSuper> 1 and #Type/string > 3 and #GCardOr = 1 and #GCardXor = 1 and #CardLone = 1 }
run example for 20 Element


