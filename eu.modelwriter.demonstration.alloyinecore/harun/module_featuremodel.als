module module_featuremodel[exactly Feature]

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








