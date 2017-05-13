open relation_model_3 as RelationModel

//abstract sig Feature extends  {}

one sig Chassis extends ModelObject {}
one sig Wiper extends ModelObject {}
one sig StaticWagon extends ModelObject {}
one sig Cabriolet extends ModelObject {}
one sig ManualControl extends ModelObject {}
one sig RearWiper extends ModelObject {}
one sig FrontWiper extends ModelObject {}
one sig RoofControl extends ModelObject {}
one sig RainSensorWiper extends ModelObject {}
one sig IntervalWiper extends ModelObject {}
one sig AutoRoofControl extends ModelObject {}
one sig RainSensor extends ModelObject {}



fact init_feature_model {
	RelationModel/FeatureModel/Root[Chassis]

	RelationModel/FeatureModel/Mandatory[Chassis -> Wiper + Cabriolet -> RoofControl + RainSensorWiper -> RainSensor + Wiper -> FrontWiper]
	RelationModel/FeatureModel/Alternative[Chassis -> (StaticWagon + Cabriolet) + FrontWiper -> (RainSensorWiper + IntervalWiper) + RoofControl -> (ManualControl + AutoRoofControl)]
	RelationModel/FeatureModel/Optional[Wiper -> RearWiper]
	RelationModel/FeatureModel/NoOr
	//RelationModel/FeatureModel/Requires[StaticWagon -> RearWiper + AutoRoofControl -> RainSensor + IntervalWiper -> StaticWagon]
	RelationModel/FeatureModel/Requires[StaticWagon -> RearWiper + AutoRoofControl -> RainSensor]
	RelationModel/FeatureModel/NoExcludes

	ConvertFeatureModel
}

run {} for exactly 8 Instance
//run {} for exactly 1 Instance
