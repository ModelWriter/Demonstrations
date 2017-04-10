/** Takes a user defined signature and defines the relations according to it. */
module module_requirementsmodel[exactly Requirement]

open util/relation
open module_featuremodel[Requirement] as FeatureModel

abstract sig RequirementsModel {
	optional: set Requirement,
	mandatory: set Requirement,

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

/** If a requirement equals to an other requirement, then these requirements have exactly the same relations */
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
private pred requires_facts[m:RequirementsModel] {
	all a,b,c: Requirement {
		b in a.(m.requires) && c in b.(m.refines) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.refines) && c in b.(m.requires) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.requires) && c in b.(m.contains) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.contains) && c in a.(m.requires) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.contains) && c in b.(m.refines) && c !in a.(m.contains + m.refines + m.partiallyRefines) => c in a.(m.requires)
	}
}

/** Defines, under what conditions program should infer that one requirement refines or partially refines another. */
private pred refines_facts[m:RequirementsModel] {
	all a,b,c: Requirement {
		b in a.(m.refines) && c in b.(m.contains) => c in a.(m.refines)
		b in a.(m.partiallyRefines) && c in b.(m.contains) => c in a.(m.partiallyRefines)
		b in a.(m.refines) && c in b.(m.partiallyRefines) => c in a.(m.partiallyRefines)
		b in a.(m.partiallyRefines) && c in b.(m.refines) => c in a.(m.partiallyRefines)
	}
}

/** Defines, under what conditions program should infer that one requirement conflicts another. */
private pred conflicts_facts[m:RequirementsModel] {
	all a,b,c: Requirement {
		b in a.(m.requires + m.refines + m.contains) && c in b.(m.conflicts) => c in a.(m.conflicts)
	}
}

/** Defines, what conditions are required to infer relations. It is to assure that program doesn't infer irrelevant relations and gives only the accurate solutions. */
private pred relation_facts[m,m': RequirementsModel] {
	all a,c: Requirement {
		c in a.(m'.requires) => c in a.*(m'.equals).*(m.requires + m.contains + m.refines).*(m'.equals)
		c in a.(m'.refines) => c in a.*(m'.equals).*(m.requires + m.refines).*(m.contains).*(m'.equals)
		c in a.(m'.equals) => c in a.*(m.equals).*(~(m.equals)).*(m.equals)
		c in a.(m'.contains) => c in a.*(m'.equals).*(m.contains).*(m'.equals)
		c in a.(m'.partiallyRefines) => c in a.*(m'.equals).*(m.refines + m.partiallyRefines).*(m.contains).*(m'.equals)
		c in a.(m'.conflicts) => 	c in a.*(m'.equals).*(m.requires + m.refines + m.contains).(m.conflicts + ~(m.conflicts)).*(m'.equals) || 
										 		c in a.*(m'.equals).(m.conflicts + ~(m.conflicts)).*~(m.requires + m.refines + m.contains).*(m'.equals)
	}
}

/** The definitions of relations. */
private pred func_definitions[m:RequirementsModel] {
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

	reflexive[m.equals, Requirement] // It was said non-reflexive in the article but it was logically wrong and gave no result.
	symmetric[m.equals]
	transitive[m.equals]
}

/** Takes the given model, places the relations into the second model and infers new relations. */
fact generateSolution {
	all m:RequirementsModel - EmptyModel |  m.mandatory = Requirement - m.optional

	GivenModel.requires in InferredModel.requires
	GivenModel.refines in InferredModel.refines
	GivenModel.contains in InferredModel.contains
	GivenModel.partiallyRefines in InferredModel.partiallyRefines
	GivenModel.conflicts in InferredModel.conflicts
	GivenModel.equals in InferredModel.equals

	func_definitions[InferredModel]
	conflicts_facts[InferredModel]
	refines_facts[InferredModel]
	requires_facts[InferredModel]
	equals_facts[InferredModel]
	functional_facts[InferredModel]
	relation_facts[GivenModel, InferredModel]

	NoRelations[EmptyModel]
}

/***********************************************************************************************************/
/***********************************************************************************************************/

/** Defines given requirements as optional and rest as mandatory. */
pred Optional[r: set Requirement] {
	all m:RequirementsModel - EmptyModel | r = m.optional
}


/** Defines all requirements as mandatory and makes sure there are no optional requirements. */
pred NoOptional {
	all m:RequirementsModel - EmptyModel | no m.optional
}

/** Defines given requirements as mandatory and rest as optional. */
pred Mandatory[r: set Requirement] {
	all m:RequirementsModel - EmptyModel | r = m.mandatory
}

/** Defines all requirements as optional and makes sure there are no mandatory requirements. */
pred NoMandatory {
	all m:RequirementsModel - EmptyModel | no m.mandatory
}

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

pred NoRelations[m: RequirementsModel] {
	no m.contains
	no m.equals
	no m.conflicts
	no m.refines
	no m.partiallyRefines
	no m.requires
	no m.mandatory
	no m.optional
}

/** Takes a feature model and converts it into this requirements model */
pred Convert[fm: FeatureModel/FeatureModel] {
	this/Requires[fm.requires + fm.mandatory]
	Refines[~(fm.(optional + alternative + mandatoryOr + optionalOr))]

	all r: ran[fm.alternative] | r.(GivenModel.conflicts) = (r.~(fm.alternative).(fm.alternative) - r) + r.(fm.excludes)
	all r: ran[GivenModel.conflicts] + dom[GivenModel.conflicts] | r in ran[fm.alternative] + ran[fm.excludes] + dom[fm.excludes]
	
	Mandatory[fm.root.*(fm.mandatory + fm.mandatoryOr)]

	NoContains
	NoPartiallyRefines
	NoEquals
}
