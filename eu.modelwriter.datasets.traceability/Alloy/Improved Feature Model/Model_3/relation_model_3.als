module relation_model_3

open feature_model_3[ModelObject] as FeatureModel
open requirements_model[ModelObject] as RequirementsModel

/** ModelObject must be extended by all the other model signatures */
abstract sig ModelObject {}

sig Optional, Mandatory in ModelObject {}

/** Converts the Feature model into a requirements model */
pred ConvertFeatureModel {
	let fm = FeatureModel/GivenFeatureModel {
		RequirementsModel/Requires[fm.requires + fm.mandatory]
		RequirementsModel/Refines[~(fm.(optional + alternative + _or))]

		all f: ModelObject | f.(RequirementsModel/GivenModel.conflicts) =  f.(fm.excludes) + (f.~(fm.alternative).(fm.alternative) - f)

		RequirementsModel/NoContains
		RequirementsModel/NoPartiallyRefines
		RequirementsModel/NoEquals

		Mandatory = FeatureModel/Root.*(fm.mandatory) // all features which are reachable from Root only by "mandatory" are mandatory in requirements model and the rest are optional.
		ModelObject - Mandatory = Optional
	}
}
