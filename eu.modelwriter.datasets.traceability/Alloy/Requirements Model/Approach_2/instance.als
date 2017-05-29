open relation_model as RelationModel

/** If we are going to combine two models into one requirements model, we need to extend its signature from ModelObject */
abstract sig Feature extends RelationModel/ModelObject {}
abstract sig Requirement extends RelationModel/ModelObject {}

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

/** We initialized our feature model here */
fact init_feature_model {
	RelationModel/FeatureModel/Root[Chassis]

	RelationModel/FeatureModel/Alternative[Chassis, StaticWagon + Cabriolet]
	RelationModel/FeatureModel/Mandatory[Chassis -> Wiper + Cabriolet -> RoofControl + RainSensorWiper -> RainSensor]
	RelationModel/FeatureModel/NoOptional
	RelationModel/FeatureModel/Alternative[Chassis -> (StaticWagon + Cabriolet) + FrontWiper -> (RainSensorWiper + IntervalWiper) + RoofControl -> (ManualControl + AutoRoofControl)]
	RelationModel/FeatureModel/OptionalOr[Wiper -> RearWiper]
	RelationModel/FeatureModel/MandatoryOr[Wiper -> FrontWiper]
	RelationModel/FeatureModel/Requires[StaticWagon -> RearWiper + AutoRoofControl -> RainSensor]
	RelationModel/FeatureModel/NoExcludes
}

/** We initialized out sysml model here */
fact init_sysml_model {
	RelationModel/SysmlModel/DeriveReqt[(SR13 + SR14) -> SR10 + SR14 -> SR11]
	RelationModel/SysmlModel/ComposedBy[(SR10 + SR11) -> SR9]
	RelationModel/SysmlModel/Copy[SR12 -> SR14]
	RelationModel/SysmlModel/NoRefines
}

/** We defined a "require" relation between elements of two models */
/** We called Relation Model's ConvertBothModels predicate with this relation as parameter */
/** So we converted two models into one requirement model and related them with this relation */
fact {
	RelationModel/ConvertBothModels[FrontWiper -> SR11]
}

run {}

check RelationModel/semantically_equals_feature_model
