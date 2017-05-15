/** Takes a user defined signature and defines the relations according to it. */
module feature_model_2[Feature]

open util/relation

one sig Root in Feature {}

abstract sig FeatureModel {
	mandatory: Feature -> Feature,
	optional: Feature -> Feature,
	alternative: Feature -> Feature,
 	_or: Feature -> Feature,

	requires: Feature -> Feature,
	excludes: Feature -> Feature
}

/** EmptyFeatureModel is the model that has no relations, GivenFeatureModel is the model that user defines */
one sig EmptyFeatureModel, GivenFeatureModel extends FeatureModel {}

fact {
	func_definitions[GivenFeatureModel]
	NoRelations[EmptyFeatureModel]
	Root.*(FeatureModel.(mandatory + optional + alternative + _or ) )= Feature // Any feature, connected to this model, must be reachable from the root.
}

private pred func_definitions[m: FeatureModel] {
	no m.mandatory & m.optional
	no m.mandatory & m.alternative
	no m.mandatory & m._or
	no m.mandatory & m.requires
	no m.mandatory & m.excludes

	no m.optional & m.alternative
	no m.optional & m._or
	no m.optional & m.requires
	no m.optional & m.excludes

	no m.alternative & m._or
	no m.alternative & m.requires
	no m.alternative & m.excludes

	no m._or & m.requires
	no m._or& m.excludes

	no m.requires & m.excludes

	no m.mandatory & ~(m.optional)
	no m.mandatory & ~(m.alternative)
	no m.mandatory & ~(m._or)
	no m.mandatory & ~(m.requires)
	no m.mandatory & ~(m.excludes)

	no m.optional & ~(m.alternative)
	no m.optional & ~(m._or)
	no m.optional & ~(m.requires)
	no m.optional & ~(m.excludes)

	no m.alternative & ~(m._or)
	no m.alternative & ~(m.requires)
	no m.alternative & ~(m.excludes)

	no m._or & ~(m.requires)
	no m._or & ~(m.excludes)

	no m.requires & ~(m.excludes)

	irreflexive[m.mandatory]
	irreflexive[m.optional]
	irreflexive[m.alternative]
	irreflexive[m._or]
	irreflexive[m.requires]
	irreflexive[m.excludes]
	antisymmetric[m.mandatory]
	antisymmetric[m.optional]
	antisymmetric[m.alternative]
	antisymmetric[m._or]
	antisymmetric[m.requires]
}

/** Possible Extensions for Configuration */

// There are instances that includes features.
sig Instance {
	includes: set Feature
}

// All configurations are unique
fact all_instances_unique {
--	all disj i, i': Instance | i.includes != i'.includes
	all i, i': Instance | i !=i' implies i.includes != i'.includes
}

fact configuration_rules {
	all i: Instance {
		Root in i.includes																																														/** root */
		all f1: Feature, f2: f1.(FeatureModel.optional) | f2 in i.includes => f1 in i.includes 																				/** optional */
		all f1: Feature, f2: f1.(FeatureModel.mandatory) | f2 in i.includes <=> f1 in i.includes 																			/** mandatory */
		all f1: Feature | f1 in i.includes and some f1.(FeatureModel._or) <=> some f1.(FeatureModel._or) & i.includes 								/** or */
		all f1: Feature | f1 in i.includes and some f1.(FeatureModel.alternative) <=> some f1.(FeatureModel.alternative) & i.includes			/** alternative (1) */
		all f1: i.includes, f2: f1.(FeatureModel.alternative), f3: f1.(FeatureModel.alternative) - f2 | !(f2 in i.includes and f3 in i.includes) 		/** alternative (2) */
		all f1: Feature, f2: f1.(FeatureModel.requires) | f1 in i.includes => f2 in i.includes																				/** requires */
		all f1: Feature, f2: f1.(FeatureModel.excludes) | !(f1 in i.includes and f2 in i.includes) 																			/** excludes */
	}
}
/** Possible Instances Extension */


pred Root[f: Feature] {
	Root = f
}

pred Mandatory[f1, f2: one Feature] {
	f1 -> f2 in GivenFeatureModel.mandatory
}

pred Optional[f1, f2: Feature] {
	f1 -> f2 in GivenFeatureModel.optional
}

pred Alternative[f1: Feature, f2: Feature] {
	f1 -> f2 in GivenFeatureModel.alternative
}

pred Or[f1, f2: Feature] {
	f1 -> f2 in GivenFeatureModel._or
}

pred Requires[f1, f2: Feature] {
	f1 -> f2 in GivenFeatureModel.requires
}

pred Excludes[f1, f2: Feature] {
	f1 -> f2 in GivenFeatureModel.excludes
}

pred Mandatory[r: Feature -> Feature] {
	r = GivenFeatureModel.mandatory
}

pred Optional[r: Feature -> Feature] {
	r = GivenFeatureModel.optional
}

pred Alternative[r: Feature -> Feature] {
	r = GivenFeatureModel.alternative
}

pred Or[r: Feature -> Feature] {
	r = GivenFeatureModel._or
}

pred Requires[r: Feature -> Feature] {
	r = GivenFeatureModel.requires
}

pred Excludes[r: Feature -> Feature] {
	r + ~r = GivenFeatureModel.excludes
}

pred NoMandatory {
	no GivenFeatureModel.mandatory
}

pred NoOptional {
	no GivenFeatureModel.optional
}

pred NoAlternative {
	no GivenFeatureModel.alternative
}

pred NoOr {
	no GivenFeatureModel._or
}

pred NoRequires {
	no GivenFeatureModel.requires
}

pred NoExcludes {
	no GivenFeatureModel.excludes
}

pred NoRelations[m: FeatureModel] {
	no m.excludes
	no m.requires
	no m._or
	no m.alternative
	no m.mandatory
	no m.optional
}
