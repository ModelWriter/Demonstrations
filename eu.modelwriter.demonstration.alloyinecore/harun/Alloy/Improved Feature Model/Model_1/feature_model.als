/** Takes a user defined signature and defines the relations according to it. */
module feature_model[Feature]

open util/relation

one sig Root in Feature {}

abstract sig FeatureModel {
	mandatory: Feature -> Feature,
	optional: Feature -> Feature,
	alternative: Feature -> Feature,
 	mandatoryOr: Feature -> Feature,
	optionalOr: Feature -> Feature,

	requires: Feature -> Feature,
	excludes: Feature -> Feature
}

/** EmptyFeatureModel is the model that has no relations, GivenFeatureModel is the model that user defines */
one sig EmptyFeatureModel, GivenFeatureModel extends FeatureModel {}

fact {
	func_definitions[GivenFeatureModel]
	NoRelations[EmptyFeatureModel]
	all f: ran[FeatureModel.(requires + excludes)] | some f.~(FeatureModel.(mandatory + optional + alternative + mandatoryOr + optionalOr))
	let rel = FeatureModel.(mandatory + optional + alternative + mandatoryOr + optionalOr + requires + excludes) | Root.*rel = ran[rel] + dom[rel] // Any feature, connected to this model, must be reachable from the root.
}

private pred func_definitions[m: FeatureModel] {
	no m.mandatory & m.optional
	no m.mandatory & m.alternative
	no m.mandatory & m.mandatoryOr
	no m.mandatory & m.optionalOr
	no m.mandatory & m.requires
	no m.mandatory & m.excludes

	no m.optional & m.alternative
	no m.optional & m.mandatoryOr
	no m.optional & m.optionalOr
	no m.optional & m.requires
	no m.optional & m.excludes

	no m.alternative & m.mandatoryOr
	no m.alternative & m.optionalOr
	no m.alternative & m.requires
	no m.alternative & m.excludes

	no m.mandatoryOr & m.optionalOr
	no m.mandatoryOr & m.requires
	no m.mandatoryOr & m.excludes

	no m.optionalOr & m.requires
	no m.optionalOr & m.excludes

	no m.requires & m.excludes

	no m.mandatory & ~(m.optional)
	no m.mandatory & ~(m.alternative)
	no m.mandatory & ~(m.mandatoryOr)
	no m.mandatory & ~(m.optionalOr)
	no m.mandatory & ~(m.requires)
	no m.mandatory & ~(m.excludes)

	no m.optional & ~(m.alternative)
	no m.optional & ~(m.mandatoryOr)
	no m.optional & ~(m.optionalOr)
	no m.optional & ~(m.requires)
	no m.optional & ~(m.excludes)

	no m.alternative & ~(m.mandatoryOr)
	no m.alternative & ~(m.optionalOr)
	no m.alternative & ~(m.requires)
	no m.alternative & ~(m.excludes)

	no m.mandatoryOr & ~(m.optionalOr)
	no m.mandatoryOr & ~(m.requires)
	no m.mandatoryOr & ~(m.excludes)

	no m.optionalOr & ~(m.requires)
	no m.optionalOr & ~(m.excludes)

	no m.requires & ~(m.excludes)

	irreflexive[m.mandatory]
	irreflexive[m.optional]
	irreflexive[m.alternative]
	irreflexive[m.mandatoryOr]
	irreflexive[m.optionalOr]
	irreflexive[m.requires]
	irreflexive[m.excludes]
	antisymmetric[m.mandatory]
	antisymmetric[m.optional]
	antisymmetric[m.alternative]
	antisymmetric[m.mandatoryOr]
	antisymmetric[m.optionalOr]
	antisymmetric[m.requires]
}

/** Possible Instances Extension */
// There are instances that includes features.
sig Instance {
	includes: set Feature
}

// There are not two equal instances.
fact all_instances_unique {
	all i: Instance, i': Instance-i | i.includes != i'.includes
}

fact diversity_rule {
	// diversity_rules_alternative_1
	diversity_rules_alternative_2
}

pred diversity_rules_alternative_1 {
	all i: Instance | Root in i.includes
	all i: Instance, f: i.includes {
		all a: f.(FeatureModel.(mandatory + mandatoryOr + requires)) | a in i.includes
		all a: f.(FeatureModel.alternative) | a in i.includes => ((a.~(FeatureModel.alternative).(FeatureModel.alternative) - a) !in i.includes) else (one (a.~(FeatureModel.alternative).(FeatureModel.alternative) - a) & i.includes)
		all a: f.(FeatureModel.optionalOr) | a !in i.includes => (some (a.~(FeatureModel.optionalOr).(FeatureModel.(optionalOr + mandatoryOr)) - a) & i.includes)
		all a: f.(FeatureModel.excludes) | a !in i.includes

		some f.~(FeatureModel.(alternative + mandatory + optional + alternative + optionalOr + mandatoryOr)) & i.includes or f = Root
	}
}

pred diversity_rules_alternative_2 {
	all i: Instance {
		 Root in i.includes																																																												/** root */
		all f1: Feature, f2: f1.(FeatureModel.optional) | f2 in i.includes => f1 in i.includes 																																		/** optional */
		all f1: Feature, f2: f1.(FeatureModel.(mandatory + mandatoryOr)) | f2 in i.includes <=> f1 in i.includes 																									/** mandatory */
		all f1: Feature | f1 in i.includes and some f1.(FeatureModel.(mandatoryOr + optionalOr)) <=> some f1.(FeatureModel.(mandatoryOr + optionalOr)) & i.includes 		/** mandatoryOr and optionalOr */
		all f1: Feature | f1 in i.includes and some f1.(FeatureModel.alternative) <=> some f1.(FeatureModel.alternative) & i.includes																	/** alternative (1) */
		all f1: i.includes, f2: f1.(FeatureModel.alternative), f3: f1.(FeatureModel.alternative) - f2 | !(f2 in i.includes and f3 in i.includes) 																/** alternative (2) */
		all f1: Feature, f2: f1.(FeatureModel.requires) | f1 in i.includes => f2 in i.includes																																		/** requires */
		all f1: Feature, f2: f1.(FeatureModel.excludes) | !(f1 in i.includes and f2 in i.includes) 																																	/** excludes */
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

pred MandatoryOr[f1, f2: Feature] {
	f1 -> f2 in GivenFeatureModel.mandatoryOr
}

pred OptionalOr[f1, f2: Feature] {
	f1 -> f2 in GivenFeatureModel.optionalOr
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

pred MandatoryOr[r: Feature -> Feature] {
	r = GivenFeatureModel.mandatoryOr
}

pred OptionalOr[r: Feature -> Feature] {
	r = GivenFeatureModel.optionalOr
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

pred NoOptionalOr {
	no GivenFeatureModel.optionalOr
}

pred NoMandatoryOr {
	no GivenFeatureModel.mandatoryOr
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
	no m.mandatoryOr
	no m.optionalOr
	no m.alternative
	no m.mandatory
	no m.optional
}
