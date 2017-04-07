/** Takes a user defined signature and defines the relations according to it. */
module module_requirementsmodel[exactly Requirement]

open util/relation
open util/ordering[Model] as models

abstract sig Model {
	requires: Requirement -> Requirement,
	refines: Requirement -> Requirement,
	contains: Requirement -> Requirement,
	partiallyRefines: Requirement -> Requirement,
	conflicts: Requirement -> Requirement,
	equals: Requirement -> Requirement
}

/** GivenModel is the model that user defines and InferredModel is the model that program infers. */
one sig GivenModel, InferredModel extends Model {}

/** There must be one relation between two requirements */
private pred functional_facts[m:Model]{
	no m.requires & m.refines
	no m.requires & m.contains
	no m.requires & m.partiallyRefines
	no m.requires & m.conflicts
	no m.requires & m.equals

	no m.refines & m.contains
	no m.refines & m.partiallyRefines
	no m.refines & m.conflicts
	no m.refines & m.equals

	no m.contains & m.partiallyRefines
	no m.contains & m.conflicts
	no m.contains & m.equals

	no m.partiallyRefines & m.conflicts
	no m.partiallyRefines & m.equals

	no m.conflicts & m.equals

	no m.requires & ~(m.refines)
	no m.requires & ~(m.contains)
	no m.requires & ~(m.partiallyRefines)
	no m.requires & ~(m.conflicts)
	no m.requires & ~(m.equals)

	no m.refines & ~(m.contains)
	no m.refines & ~(m.partiallyRefines)
	no m.refines & ~(m.conflicts)
	no m.refines & ~(m.equals)

	no m.contains & ~(m.partiallyRefines)
	no m.contains & ~(m.conflicts)
	no m.contains & ~(m.equals)

	no m.partiallyRefines & ~(m.conflicts)
	no m.partiallyRefines & ~(m.equals)

	no m.conflicts & ~(m.equals)
}

/** If a requirement equals to an other requirement, then these requirements have exactly the same relations */
private pred equals_facts[m:Model] {
	all a,b: Requirement {
		b in a.(m.equals) => a.(m.conflicts) = b.(m.conflicts)
		b in a.(m.equals) => a.(m.requires) = b.(m.requires)
		b in a.(m.equals) => a.(m.equals) = b.(m.equals)
		b in a.(m.equals) => a.(m.refines) = b.(m.refines)
		b in a.(m.equals) => a.(m.partiallyRefines) = b.(m.partiallyRefines)
		b in a.(m.equals) => a.(m.contains) = b.(m.contains)

		b in a.(m.equals) => a.~(m.conflicts) = b.~(m.conflicts)
		b in a.(m.equals) => a.~(m.requires) = b.~(m.requires)
		b in a.(m.equals) => a.~(m.equals) = b.~(m.equals)
		b in a.(m.equals) => a.~(m.refines) = b.~(m.refines)
		b in a.(m.equals) => a.~(m.partiallyRefines) = b.~(m.partiallyRefines)
		b in a.(m.equals) => a.~(m.contains) = b.~(m.contains)
	}
}

/** Defines, under what conditions program should infer that one requirement requires another. */
private pred req_ref_facts[m:Model] {
	all a,b,c: Requirement {
		b in a.(m.requires) && c in b.(m.refines) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.refines) && c in b.(m.requires) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.requires) && c in b.(m.contains) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.contains) && c in a.(m.requires) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.contains) && c in b.(m.refines) && c !in a.(m.contains) + a.(m.refines) + a.(m.partiallyRefines) => c in a.(m.requires)
	}
}

/** Defines, under what conditions program should infer that one requirement refines or partially refines another. */
private pred ref_cont_facts[m:Model] {
	all a,b,c: Requirement {
		b in a.(m.refines) && c in b.(m.contains) => c in a.(m.refines)
		b in a.(m.partiallyRefines) && c in b.(m.contains) => c in a.(m.partiallyRefines)
		b in a.(m.refines) && c in b.(m.partiallyRefines) => c in a.(m.partiallyRefines)
		b in a.(m.partiallyRefines) && c in b.(m.refines) => c in a.(m.partiallyRefines)
	}
}

/** Defines, under what conditions program should infer that one requirement conflicts another. */
private pred req_conf_facts[m:Model] {
	all a,b,c: Requirement {
		b in a.(m.requires) && c in b.(m.conflicts) => c in a.(m.conflicts)
		b in a.(m.refines) && c in b.(m.conflicts) => c in a.(m.conflicts)
		b in a.(m.contains) && c in b.(m.conflicts) => c in a.(m.conflicts)
	}
}

/** Defines, what conditions are required to infer relations. It is to assure that program doesn't infer irrelevant relations and gives only the accurate solutions. */
private pred relation_facts[m,m' : Model] {
	all a,c: Requirement {
		c in a.(m'.requires) => c in a.*(m'.equals).*(m.requires).*(m.contains).*(m.refines).*(m.contains).*(m.requires).*(m'.equals)
		c in a.(m'.refines) => c in a.*(m'.equals).*(m.requires).*(m.refines).*(m.requires).*(m.contains).*(m'.equals)
		c in a.(m'.equals) => c in a.*(m.equals).*(~(m.equals)).*(m.equals)
		c in a.(m'.contains) => c in a.*(m'.equals).*(m.contains).*(m'.equals)
		c in a.(m'.partiallyRefines) => c in a.*(m'.equals).*(m.refines).*(m.partiallyRefines).*(m.refines).*(m.contains).*(m'.equals)
		c in a.(m'.conflicts) => 	c in a.*(m'.equals).*(m.requires).*(m.refines).*(m.requires).(m.conflicts).*(m'.equals) 	|| 
												c in a.*(m'.equals).*(m.requires).*(m.refines).*(m.requires).~(m.conflicts).*(m'.equals) ||
										 		c in a.*(m'.equals).(m.conflicts).*~(m.requires).*(~(m.refines)).*(~(m.requires)).*(m'.equals) || 
												c in a.*(m'.equals).~(m.conflicts).*~(m.requires).*(~(m.refines)).*(~(m.requires)).*(m'.equals) 
	}
}

/** The definitions of relations. */
private pred func_definitions[m:Model] {
	irreflexive[m.requires]
	antisymmetric[m.requires]
	transitive[m.requires]

	irreflexive[m.refines]
	antisymmetric[m.refines]
	transitive[m.refines]

	irreflexive[m.contains]
	antisymmetric[m.contains]
	transitive[m.contains]

	irreflexive[m.partiallyRefines]
	antisymmetric[m.partiallyRefines]
	transitive[m.partiallyRefines]

	irreflexive[m.conflicts]
	symmetric[m.conflicts]

	reflexive[m.equals, Requirement] // It was said non-reflexive in the article but it is logically wrong and gives no result.
	symmetric[m.equals]
	transitive[m.equals]
}

/** Takes the given model, places the relations into the second model and infers new relations. */
fact generateSolution {
	one m0:Model, m1: models/next[m0] {

		m0 = GivenModel

		m0.requires in m1.requires
		m0.refines in m1.refines
		m0.contains in m1.contains
		m0.partiallyRefines in m1.partiallyRefines
		m0.conflicts in m1.conflicts
		m0.equals in m1.equals

		func_definitions[m1]
		req_conf_facts[m1]
		ref_cont_facts[m1]
		req_ref_facts[m1]
		equals_facts[m1]
		functional_facts[m1]
		relation_facts[m0,m1]
	}
}

/***********************************************************************************************************/
/***********************************************************************************************************/

/** Makes sure that r1 requires r2 */
pred Requires[r1,r2: Requirement] { 
	let m0 = models/first {
		r1 -> r2 in m0.requires
	}
}

/** Makes sure that r1 refines r2 */
pred Refines[r1,r2: Requirement] { 
	let m0 = models/first {
		r1 -> r2 in m0.refines
	}
}

/** Makes sure that r1 partially refines r2 */
pred PartiallyRefines[r1,r2: Requirement] { 
	let m0 = models/first {
		r1 -> r2 in m0.partiallyRefines
	}
}

/** Makes sure that r1 conflicts r2 */
pred Conflicts[r1,r2: Requirement] { 
	let m0 = models/first {
		r1 -> r2 in m0.conflicts
	}
}

/** Makes sure that r1 equals r2 */
pred Equals[r1,r2: Requirement] { 
	let m0 = models/first {
		r1 -> r2 in m0.equals
	}
}

/** Makes sure that r1 contains r2 */
pred Contains[r1,r2: Requirement] { 
	let m0 = models/first {
		r1 -> r2 in m0.contains
	}
}

/** Takes a set of relations and makes it equal to requires relation in the user defined model */
pred Requires[r: Requirement -> Requirement]{
	let m0 = models/first {
		r = m0.requires
	}
}

/** Takes a set of relations and makes it equal to refines relation in the user defined model */
pred Refines[r: Requirement -> Requirement]{
	let m0 = models/first {
		r = m0.refines
	}
}

/** Takes a set of relations and makes it equal to partially refines relation in the user defined model */
pred PartiallyRefines[r: Requirement -> Requirement]{
	let m0 = models/first {
		r = m0.partiallyRefines
	}
}

/** Takes a set of relations and makes it equal to conflicts relation in the user defined model */
pred Conflicts[r: Requirement -> Requirement]{
	let m0 = models/first {
		r = m0.conflicts
	}
}

/** Takes a set of relations and makes it equal to equals relation in the user defined model */
pred Equals[r: Requirement -> Requirement]{
	let m0 = models/first {
		r = m0.equals
	}
}

/** Takes a set of relations and makes it equal to conflicts relation in the user defined model */
pred Contains[r: Requirement -> Requirement]{
	let m0 = models/first {
		r = m0.contains
	}
}

/** Makes sure that there is no requires relation in the user defined model */
pred NoRequires {
	let m0 = models/first {
		no m0.requires
	}
}

/** Makes sure that there is no refines relation in the user defined model */
pred NoRefines {
	let m0 = models/first {
		no m0.refines
	}
}

/** Makes sure that there is no partially refines relation in the user defined model */
pred NoPartiallyRefines {
	let m0 = models/first {
		no m0.partiallyRefines
	}
}

/** Makes sure that there is no conflicts relation in the user defined model */
pred NoConflicts {
	let m0 = models/first {
		no m0.conflicts
	}
}

/** Makes sure that there is no equals relation in the user defined model */
pred NoEquals {
	let m0 = models/first {
		no m0.equals
	}
}

/** Makes sure that there is no contains relation in the user defined model */
pred NoContains {
	let m0 = models/first {
		no m0.contains
	}
}
