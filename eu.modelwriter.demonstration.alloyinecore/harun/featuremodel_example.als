open module_featuremodel[Feature] as FeatureModel
open module_requirementsmodel[Feature] as RequirementsModel

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

pred init_feature_model {
	FeatureModel/Root[Chassis]

	FeatureModel/Mandatory[Chassis -> Wiper + Cabriolet -> RoofControl + RainSensorWiper -> RainSensor]
	FeatureModel/NoOptional
	FeatureModel/Alternative[Chassis -> (StaticWagon + Cabriolet) + FrontWiper -> (RainSensorWiper + IntervalWiper) + RoofControl -> (ManualControl + AutoRoofControl)]
	FeatureModel/OptionalOr[Wiper -> RearWiper]
	FeatureModel/MandatoryOr[Wiper -> FrontWiper]
	FeatureModel/Requires[StaticWagon -> RearWiper + AutoRoofControl -> RainSensor]
	FeatureModel/NoExcludes
}

pred init_requirements_model {
	RequirementsModel/Requires[Chassis -> Wiper + StaticWagon -> RearWiper + Cabriolet -> RoofControl + AutoRoofControl -> RainSensor + RainSensorWiper ->  RainSensor]
	RequirementsModel/Refines[Cabriolet -> Chassis + StaticWagon -> Chassis + RearWiper -> Wiper + FrontWiper -> Wiper + IntervalWiper -> FrontWiper + RainSensorWiper -> FrontWiper + ManualControl -> RoofControl + AutoRoofControl -> RoofControl]  
	RequirementsModel/Conflicts[StaticWagon -> Cabriolet + ManualControl -> AutoRoofControl + IntervalWiper -> RainSensorWiper]
	RequirementsModel/NoPartiallyRefines
	RequirementsModel/NoEquals
	RequirementsModel/NoContains

	RequirementsModel/Optional[StaticWagon + Cabriolet + RoofControl + ManualControl + AutoRoofControl + RearWiper + IntervalWiper + RainSensor]
}

pred init {
	init_feature_model
	init_requirements_model
}

pred convert_to_requirements_model {
	init_feature_model
	RequirementsModel/Convert[FeatureModel/Model]
}

run init
run convert_to_requirements_model

assert semanticly_equals {
	init
	let fm = FeatureModel/Model, rm = RequirementsModel/GivenModel {
		fm.(requires + mandatory + optional) in rm.(requires + refines + contains)
		all f: Feature, f': f.(rm.conflicts) | f.~(fm.(alternative + mandatoryOr + optionalOr)) = f'.~(fm.(alternative + mandatoryOr + optionalOr)) || f in f'.(fm.excludes) +  f'.~(fm.excludes)
		all f: Feature, f': f.(rm.refines) | f in f'.(fm.(alternative + mandatoryOr + optionalOr))
		all f: rm.optional | some f.~*(fm.(alternative + optionalOr + optional))
		all f: rm.mandatory | some f.~*(fm.(mandatoryOr + mandatory)) || f = fm.root
	}
}

check semanticly_equals
