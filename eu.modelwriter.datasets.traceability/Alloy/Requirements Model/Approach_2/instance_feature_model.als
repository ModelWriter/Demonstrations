open feature_model[Feature] as FeatureModel
open util/ordering[Instance]

abstract sig Feature {}

one sig Chassis extends Feature {}
one sig Wiper extends Feature {}
one sig StaticWagon extends Feature {}
one sig Cabriolet extends Feature {}
one sig ManualControl extends Feature {}
one sig RearWiper extends Feature {}
one sig FrontWiper extends Feature {}
one sig RoofControl extends Feature {}
one sig RainSensorWiper extends Feature {}
one sig IntervalWiper extends Feature {}
one sig AutoRoofControl extends Feature {}
one sig RainSensor extends Feature {}

fact init_feature_model {
	FeatureModel/Root[Chassis]

	FeatureModel/Mandatory[Chassis -> Wiper + Cabriolet -> RoofControl + RainSensorWiper -> RainSensor]
	FeatureModel/NoOptional
	FeatureModel/Alternative[Chassis -> (StaticWagon + Cabriolet) + FrontWiper -> (RainSensorWiper + IntervalWiper) + RoofControl -> (ManualControl + AutoRoofControl)]
	FeatureModel/OptionalOr[Wiper -> RearWiper]
	FeatureModel/MandatoryOr[Wiper -> FrontWiper]
	FeatureModel/Requires[StaticWagon -> RearWiper + AutoRoofControl -> RainSensor]
	FeatureModel/NoExcludes
}

/** -------------------------------------------- */



sig Instance {
	includes: set Feature
}

fact root_is_included {
	all i: Instance | FeatureModel/Root in i.includes
}

fact all_instances_unique {
	all i: Instance, i': Instance-i | i.includes != i'.includes
}

fact variation_rules {
	all i: Instance, f: i.includes {
		all a: f.(FeatureModel.(mandatory + mandatoryOr + requires)) | a in i.includes
		all a: f.(FeatureModel.alternative) | a in i.includes => ((a.~(FeatureModel.alternative).(FeatureModel.alternative) - a) !in i.includes) else (one (a.~(FeatureModel.alternative).(FeatureModel.alternative) - a) & i.includes)
		all a: f.(FeatureModel.optionalOr) | a !in i.includes => (some (a.~(FeatureModel.optionalOr).(FeatureModel.(optionalOr + mandatoryOr)) - a) & i.includes)
		all a: f.(FeatureModel.excludes) | a !in i.includes

		some f.~(FeatureModel.(alternative + mandatory + optional + alternative + optionalOr + mandatoryOr + requires)) & i.includes or f = Root
	}
}


/** -------------------------------------------- */

run {} for 5 Instance
