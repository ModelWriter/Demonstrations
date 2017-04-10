open module_featuremodel[Feature] as FeatureModel
open module_model[Feature] as Model

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

fact convert_to_requirements_model {	init_feature_model }

run {}

check Model/semantically_equals

