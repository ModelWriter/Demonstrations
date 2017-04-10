module module_featuremodel[exactly Feature]

open util/relation

one sig Model {
	root: Feature,

	mandatory: Feature -> Feature,
	optional: Feature -> Feature,
	alternative: Feature -> Feature,
 	mandatoryOr: Feature -> Feature,
	optionalOr: Feature -> Feature,

	requires: Feature -> Feature,
	excludes: Feature -> Feature
}

fact {
	func_def[Model]
	Model.root.*(Model.(mandatory + optional + alternative + mandatoryOr + optionalOr + requires + excludes)) = Feature
}

pred func_def[m: Model] {
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
	Model.root = f
}

pred Mandatory[f1, f2: Feature] {
	f1 -> f2 in Model.mandatory
}

pred Optional[f1, f2: Feature] {
	f1 -> f2 in Model.optional
}

pred Alternative[f1: Feature, f2: Feature] {
	f1 -> f2 in Model.alternative
}

pred MandatoryOr[f1, f2: Feature] {
	f1 -> f2 in Model.mandatoryOr
}

pred OptionalOr[f1, f2: Feature] {
	f1 -> f2 in Model.optionalOr
}

pred Requires[f1, f2: Feature] {
	f1 -> f2 in Model.requires
}

pred Excludes[f1, f2: Feature] {
	f1 -> f2 in Model.excludes
}

pred Mandatory[r: Feature -> Feature] {
	r = Model.mandatory
}

pred Optional[r: Feature -> Feature] {
	r = Model.optional
}

pred Alternative[r: Feature -> Feature] {
	r = Model.alternative
}

pred MandatoryOr[r: Feature -> Feature] {
	r = Model.mandatoryOr
}

pred OptionalOr[r: Feature -> Feature] {
	r = Model.optionalOr
}

pred Requires[r: Feature -> Feature] {
	r = Model.requires
}

pred Excludes[r: Feature -> Feature] {
	r = Model.excludes
}

pred NoMandatory {
	no Model.mandatory
}

pred NoOptional {
	no Model.optional
}

pred NoAlternative {
	no Model.alternative
}

pred NoOptionalOr {
	no Model.optionalOr
}

pred NoMandatoryOr {
	no Model.mandatoryOr
}

pred NoRequires {
	no Model.requires
}

pred NoExcludes {
	no Model.excludes
}
