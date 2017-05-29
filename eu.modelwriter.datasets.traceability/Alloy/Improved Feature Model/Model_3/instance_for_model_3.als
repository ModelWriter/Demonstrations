open combined_feature_model as Combined

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
	Combined/FeatureModel/Root[Chassis]

	Combined/FeatureModel/Mandatory[Chassis -> Wiper + Cabriolet -> RoofControl + RainSensorWiper -> RainSensor + Wiper -> FrontWiper]
	Combined/FeatureModel/Alternative[Chassis -> (StaticWagon + Cabriolet) + FrontWiper -> (RainSensorWiper + IntervalWiper) + RoofControl -> (ManualControl + AutoRoofControl)]
	Combined/FeatureModel/Optional[Wiper -> RearWiper]
	Combined/FeatureModel/NoOr
	Combined/FeatureModel/Requires[StaticWagon -> RearWiper + AutoRoofControl -> RainSensor]
	Combined/FeatureModel/NoExcludes

	ConvertFeatureModel
}

run {} for exactly 8 Configuration
