/** Takes a user defined signature and defines the relations according to it. */
module requirements_model[Requirement]

open util/relation

abstract sig RequirementsModel {
	requires: Requirement -> Requirement,
	refines: Requirement -> Requirement,
	contains: Requirement -> Requirement,
	partiallyRefines: Requirement -> Requirement,
	conflicts: Requirement -> Requirement,
	equals: Requirement -> Requirement
}

/** EmptyModel is the model that has no relations, GivenModel is the model that user defines and InferredModel is the model that program infers. */
one sig EmptyModel, GivenModel, InferredModel extends RequirementsModel {}

/** There must be one relation between two requirements */
private pred functional_facts[m:RequirementsModel]{
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

/** If a requirement equals to another requirement, then these requirements have exactly the same relations */
private pred equals_facts[m:RequirementsModel] {
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
private pred infer_requires_facts[m:RequirementsModel] {
	all a,b,c: Requirement {
		b in a.(m.requires) && c in b.(m.refines) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.refines) && c in b.(m.requires) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.requires) && c in b.(m.contains) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.contains) && c in a.(m.requires) &&  c !in a.(m.contains) => c in a.(m.requires)
	}
}

/** Defines, under what conditions program should infer that one requirement refines another. */
private pred infer_refines_facts[m:RequirementsModel] {
	//all a,b,c: Requirement {
	//	
	//}
}

/** Defines, under what conditions program should infer that one requirement partially refines another. */
private pred infer_partiallyrefines_facts[m:RequirementsModel] {
	all a,b,c: Requirement {
		b in a.(m.contains) && c in b.(m.refines) => c in a.(m.partiallyRefines)
		b in a.(m.refines) && c in b.(m.contains) => c in a.(m.partiallyRefines)
		b in a.(m.partiallyRefines) && c in b.(m.contains) => c in a.(m.partiallyRefines)
		b in a.(m.contains) && c in b.(m.partiallyRefines) => c in a.(m.partiallyRefines)
		b in a.(m.refines) && c in b.(m.partiallyRefines) => c in a.(m.partiallyRefines)
		b in a.(m.partiallyRefines) && c in b.(m.refines) => c in a.(m.partiallyRefines)
	}
}

/** Defines, under what conditions program should infer that one requirement conflicts another. */
private pred infer_conflicts_facts[m:RequirementsModel] {
	all a,b,c: Requirement {
		b in a.(m.requires + m.refines + m.contains) && c in b.(m.conflicts) => c in a.(m.conflicts)
	}
}

/** Defines, what conditions are required to infer relations. It assures that program doesn't infer irrelevant relations and gives only the accurate solutions. */
private pred relation_facts[m,m': RequirementsModel] {
	all a,c: Requirement {
		c in a.(m'.equals) => c in a.*(m.equals + ~(m.equals))
		c in a.(m'.requires) => c in a.*(m.requires + m.contains + m.refines + m'.equals) // If "a" requires "c" in the inferred model, then we must somehow reach "c" from "a" in the given model by using requires, contains and refines relations.
		c in a.(m'.refines) => c in a.*(m.requires + m.refines + m'.equals).*(m.contains + m'.equals) // Same logic here.
		c in a.(m'.contains) => c in a.*(m.contains + m'.equals) // Same logic here.
		c in a.(m'.partiallyRefines) => c in a.*(m.(refines + partiallyRefines) + m'.equals).*(m.contains + m'.equals) // Same logic here.
		c in a.(m'.conflicts) => 	c in a.(m.requires + m.refines + m.contains + m'.equals).(m.conflicts + ~(m.conflicts)).*(m'.equals) || // If a conflicts with c in the inferred model, then in the given model, either a conflicts with c or what is required by a, conflicts with c.
										 		c in a.*(m'.equals).(m.conflicts + ~(m.conflicts)).*~(m.requires + m.refines + m.contains + m'.equals)	// Reverse logic here.
	}
}

/** The definitions of relations. */
private pred relation_properties[m':RequirementsModel] {
	irreflexive[m'.requires]
	antisymmetric[m'.requires]
	transitive[m'.requires]

	irreflexive[m'.refines]
	antisymmetric[m'.refines]
	transitive[m'.refines]

	irreflexive[m'.contains]
	antisymmetric[m'.contains]
	transitive[m'.contains]

	irreflexive[m'.partiallyRefines]
	antisymmetric[m'.partiallyRefines]
	transitive[m'.partiallyRefines]

	irreflexive[m'.conflicts]
	symmetric[m'.conflicts]

	reflexive[m'.equals, Requirement] // It was said non-reflexive in the article but it was logically wrong and gave no result.
	symmetric[m'.equals]
	transitive[m'.equals]
}

/** Takes the given model, places the relations into the second model and infers new relations. */
fact generateSolution {
	GivenModel.requires in InferredModel.requires
	GivenModel.refines in InferredModel.refines
	GivenModel.contains in InferredModel.contains
	GivenModel.partiallyRefines in InferredModel.partiallyRefines
	GivenModel.conflicts in InferredModel.conflicts
	GivenModel.equals in InferredModel.equals

	relation_properties[InferredModel]
	infer_conflicts_facts[InferredModel]
	infer_refines_facts[InferredModel]
	infer_partiallyrefines_facts[InferredModel]
	infer_requires_facts[InferredModel]
	equals_facts[InferredModel]
	functional_facts[InferredModel]
	relation_facts[GivenModel, InferredModel]

	NoRelations[EmptyModel]
}

/***********************************************************************************************************/
/***********************************************************************************************************/

/** Makes sure that r1 requires r2 */
pred Requires[r1,r2: Requirement] { 
	r1 -> r2 in GivenModel.requires
}

/** Makes sure that r1 refines r2 */
pred Refines[r1,r2: Requirement] { 
	r1 -> r2 in GivenModel.refines
}

/** Makes sure that r1 partially refines r2 */
pred PartiallyRefines[r1,r2: Requirement] { 
	r1 -> r2 in GivenModel.partiallyRefines
}

/** Makes sure that r1 conflicts r2 */
pred Conflicts[r1,r2: Requirement] { 
	r1 -> r2 in GivenModel.conflicts
}

/** Makes sure that r1 equals r2 */
pred Equals[r1,r2: Requirement] { 
	r1 -> r2 in GivenModel.equals
}

/** Makes sure that r1 contains r2 */
pred Contains[r1,r2: Requirement] { 
	r1 -> r2 in GivenModel.contains
}

/** Takes a set of relations and makes it equal to requires relation in the user defined model */
pred Requires[r: Requirement -> Requirement]{
	r = GivenModel.requires
}

/** Takes a set of relations and makes it equal to refines relation in the user defined model */
pred Refines[r: Requirement -> Requirement]{
	r = GivenModel.refines
}

/** Takes a set of relations and makes it equal to partially refines relation in the user defined model */
pred PartiallyRefines[r: Requirement -> Requirement]{
	r = GivenModel.partiallyRefines
}

/** Takes a set of relations and makes it equal to conflicts relation in the user defined model */
pred Conflicts[r: Requirement -> Requirement]{
	r = GivenModel.conflicts
}

/** Takes a set of relations and makes it equal to equals relation in the user defined model */
pred Equals[r: Requirement -> Requirement]{
	r = GivenModel.equals
}

/** Takes a set of relations and makes it equal to conflicts relation in the user defined model */
pred Contains[r: Requirement -> Requirement]{
	r = GivenModel.contains
}

/** Makes sure that there are no requires relations in the user defined model */
pred NoRequires {
	no GivenModel.requires
}

/** Makes sure that there are no refines relations in the user defined model */
pred NoRefines {
	no GivenModel.refines
}

/** Makes sure that there are no partially refines relations in the user defined model */
pred NoPartiallyRefines {
	no GivenModel.partiallyRefines
}

/** Makes sure that there are no conflicts relations in the user defined model */
pred NoConflicts {
	no GivenModel.conflicts
}

/** Makes sure that there are no equals relations in the user defined model */
pred NoEquals {
	no GivenModel.equals
}

/** Makes sure that there are no contains relations in the user defined model */
pred NoContains {
	no GivenModel.contains
}

/** Makes sure that there are no relations in requirements model given as parameter */
pred NoRelations[m: RequirementsModel] {
	no m.contains
	no m.equals
	no m.conflicts
	no m.refines
	no m.partiallyRefines
	no m.requires
}
