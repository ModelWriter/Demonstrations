module combined_feature_model

open feature_model_3[Feature] as FeatureModel
open requirements_model[Feature] as RequirementsModel

/** ModelObject must be extended by all the other model signatures */
abstract sig Feature {}

sig Optional, Mandatory in Feature {}

/** Converts the Feature model into a requirements model */
pred ConvertFeatureModel {
	let fm = FeatureModel/GivenFeatureModel {
		RequirementsModel/Requires[fm.requires + fm.mandatory]
		RequirementsModel/Refines[~(fm.(optional + alternative + _or))]

		all f: Feature | f.(RequirementsModel/GivenModel.conflicts) =  f.(fm.excludes) + (f.~(fm.alternative).(fm.alternative) - f)

		RequirementsModel/NoContains
		RequirementsModel/NoPartiallyRefines
		RequirementsModel/NoEquals

		Mandatory = FeatureModel/Root.*(fm.mandatory) // all features which are reachable from Root only by "mandatory" are mandatory in requirements model and the rest are optional.
		Feature - Mandatory = Optional
	}
}
