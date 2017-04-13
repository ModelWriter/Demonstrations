/** Takes a user defined signature and defines the relations according to it. */
module module_featuremodel[Feature]

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

/** EmptyFeatureModel is the model that has no relations but root, GivenFeatureModel is the model that user defines */
one sig EmptyFeatureModel, GivenFeatureModel extends FeatureModel {}

fact {
	func_definitions[GivenFeatureModel]
	NoRelations[EmptyFeatureModel]
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

pred Root[f: Feature] {
	Root = f
}

pred Mandatory[f1, f2: Feature] {
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
	r = GivenFeatureModel.excludes
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
