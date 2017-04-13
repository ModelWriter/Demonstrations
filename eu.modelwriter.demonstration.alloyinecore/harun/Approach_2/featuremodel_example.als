open module_featuremodel[Object] as FeatureModel
open module_sysmlmodel[Object] as SysmlModel
open module_model[Object] as Model

abstract sig Object {}
abstract sig Feature extends Object {}
abstract sig Requirement extends Object {}

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

one sig SR9 extends Requirement {}
one sig SR10 extends Requirement {}
one sig SR11 extends Requirement{}
one sig SR12 extends Requirement {}
one sig SR13 extends Requirement {}
one sig SR14 extends Requirement {}

fact init_feature_model {
	Model/FeatureModel/Root[Chassis]

	FeatureModel/Mandatory[Chassis -> Wiper + Cabriolet -> RoofControl + RainSensorWiper -> RainSensor]
	FeatureModel/NoOptional
	FeatureModel/Alternative[Chassis -> (StaticWagon + Cabriolet) + FrontWiper -> (RainSensorWiper + IntervalWiper) + RoofControl -> (ManualControl + AutoRoofControl)]
	FeatureModel/OptionalOr[Wiper -> RearWiper]
	FeatureModel/MandatoryOr[Wiper -> FrontWiper]
	FeatureModel/Requires[StaticWagon -> RearWiper + AutoRoofControl -> RainSensor]
	FeatureModel/NoExcludes
}

fact init_sysml_model {
	SysmlModel/DeriveReqt[(SR13 + SR14) -> SR10 + SR14 -> SR11]
	SysmlModel/ComposedBy[(SR10 + SR11) -> SR9]
	SysmlModel/Copy[SR12 -> SR14]
	SysmlModel/NoRefines
}

fact {
	Model/ConvertBothModels
}

run {}

check Model/semantically_equals_feature_model
