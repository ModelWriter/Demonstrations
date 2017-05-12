module relation_model_2

open feature_model_2[ModelObject] as FeatureModel
open sysml_model[ModelObject] as SysmlModel
open requirements_model[ModelObject] as RequirementsModel

/** ModelObject must be extended by all the other model signatures */
abstract sig ModelObject {}

sig Optional, Mandatory in ModelObject {}

/** Converts the Feature model into a requirements model */
pred ConvertFeatureModel {
	let fm = FeatureModel/GivenFeatureModel {
		RequirementsModel/Requires[fm.requires + fm.mandatory]
		RequirementsModel/Refines[~(fm.(optional + alternative + _or))]

		all r: ran[fm.alternative] | r.(RequirementsModel/GivenModel.conflicts) = (r.~(fm.alternative).(fm.alternative) - r) + r.(fm.excludes) // for all features which are in the range of "alternative", these features conflict with the features which have the same range of "~alternative" and the features which are in its "excludes" relation.                 
		all r: ran[RequirementsModel/GivenModel.conflicts] + dom[RequirementsModel/GivenModel.conflicts] | r in ran[fm.alternative] + ran[fm.excludes] + dom[fm.excludes] // for all features in the 'domain and range' of "conflicts", these features ar in the 'range' of "alternative" or in the 'range or domain' of "excludes"

		RequirementsModel/NoContains
		RequirementsModel/NoPartiallyRefines
		RequirementsModel/NoEquals

		Mandatory = FeatureModel/Root.*(fm.mandatory) // all features which are reachable from Root only by "mandatory" or "mandatoryOr" are mandatory in requirements model and the rest are optional.
		ModelObject - Mandatory = Optional
	}
}

/** Converts the SysML model into a requirements model */
pred ConvertSysmlModel {
	let sm = SysmlModel/GivenSysmlModel {
		RequirementsModel/Requires[sm.deriveReqt]
		RequirementsModel/Refines[sm.refines]
		RequirementsModel/Contains[~(sm.composedBy)]
		RequirementsModel/Equals[sm.copy]

		RequirementsModel/NoPartiallyRefines
		RequirementsModel/NoConflicts
		no Mandatory
		no Optional
	}
}

/** Converts the Feature model and the SysML model into requirements models and combines them with no relations between two model's elements */
pred ConvertBothModels {
	let sm = SysmlModel/GivenSysmlModel,  fm = FeatureModel/GivenFeatureModel {
		RequirementsModel/Requires[fm.requires + fm.mandatory + sm.deriveReqt]
		RequirementsModel/Refines[~(fm.(optional + alternative + _or)) + sm.refines]
		RequirementsModel/Contains[~(sm.composedBy)]
		RequirementsModel/Equals[sm.copy]
		RequirementsModel/NoPartiallyRefines
		all r: ran[fm.alternative] | r.(RequirementsModel/GivenModel.conflicts) = (r.~(fm.alternative).(fm.alternative) - r) + r.(fm.excludes) // for all features which are in the range of "alternative", these features conflict with the features which have the same range of "~alternative" and the features which are in its "excludes" relation.                 
		all r: ran[RequirementsModel/GivenModel.conflicts] + dom[RequirementsModel/GivenModel.conflicts] | r in ran[fm.alternative] + ran[fm.excludes] + dom[fm.excludes] // for all features in the 'domain and range' of "conflicts", these features are in the 'range' of "alternative" or in the 'range or domain' of "excludes"
		Optional = FeatureModel/Root.*(fm.mandatory).(fm.alternative + fm.optional + fm._or).*(fm.mandatory + fm._or + fm.alternative + fm.optional) // all features which are reachable from Root with at least one "fm.alternative", "fm.optional" or "fm.optionalOr" are optional and the rest are mandatory.
		Mandatory = FeatureModel/Root.*(fm.mandatory)
	}
}

/** Converts the Feature model and the SysML model into requirements models and combines them with user given "require" relations */
pred ConvertBothModels[rel: ModelObject -> ModelObject] {
	let sm = SysmlModel/GivenSysmlModel,  fm = FeatureModel/GivenFeatureModel {
		RequirementsModel/Requires[fm.requires + fm.mandatory + sm.deriveReqt + rel]
		RequirementsModel/Refines[~(fm.(optional + alternative + _or)) + sm.refines]
		RequirementsModel/Contains[~(sm.composedBy)]
		RequirementsModel/Equals[sm.copy]
		RequirementsModel/NoPartiallyRefines // Neither sysml model nor feature model uses partially refines relation of requirements model.
		all r: ran[fm.alternative] | r.(RequirementsModel/GivenModel.conflicts) = (r.~(fm.alternative).(fm.alternative) - r) + r.(fm.excludes) // for all features which are in the range of "alternative", these features conflict with the features which have the same range of "~alternative" and the features which are in its "excludes" relation.                 
		all r: ran[RequirementsModel/GivenModel.conflicts] + dom[RequirementsModel/GivenModel.conflicts] | r in ran[fm.alternative] + ran[fm.excludes] + dom[fm.excludes] // for all features in the 'domain and range' of "conflicts", these features ar in the 'range' of "alternative" or in the 'range or domain' of "excludes"
		Optional = FeatureModel/Root.*(fm.mandatory).(fm.alternative + fm.optional + fm._or).*(fm.mandatory + fm._or+ fm.alternative + fm.optional) // all features which are reachable from Root with at least one "fm.alternative", "fm.optional" or "fm.optionalOr" are optional and the rest are mandatory.
		Mandatory = FeatureModel/Root.*(fm.mandatory)
	}
}
