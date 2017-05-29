open combined_feature_model as Combined

one sig Automobile extends Feature {}

one sig Chassis extends Feature {}
one sig AirConditioner extends Feature {}
one sig GearBox extends Feature{}
one sig EnergyReservoir extends Feature{}

one sig Wiper extends Feature {}
one sig StationWagon extends Feature {}
one sig Cabriolet extends Feature {}
one sig ClimateControl extends Feature {}
one sig ManualControl extends Feature {}
one sig AutoGearBox extends Feature {}
one sig ManualGearBox extends Feature {}
one sig _4x4GearBox extends Feature {}
one sig Accumulator extends Feature {}
one sig GasolineTank extends Feature {}

one sig RearWiper extends Feature {}
one sig FrontWiper extends Feature {}
one sig RoofControl extends Feature {}
one sig Engine extends Feature {}

one sig RainSensorWiper extends Feature {}
one sig IntervalWiper extends Feature {}
one sig ManualRoofControl extends Feature {}
one sig AutoRoofControl extends Feature {}
one sig EngineKind extends Feature {}
one sig EngineSize extends Feature {}

one sig RainSensor extends Feature {}
one sig Gasoline extends Feature {}
one sig Diesel extends Feature {}
one sig Hybrid extends Feature {}
one sig Electric extends Feature {}
one sig _4Cylinders extends Feature {}
one sig _6Cylinders extends Feature {}
one sig _8Cylinders extends Feature {}

fact init_feature_model {
	Combined/FeatureModel/Root[Automobile]

	Combined/FeatureModel/Mandatory[Automobile -> (Chassis + GearBox + EnergyReservoir + Engine) + Chassis -> Wiper + Engine -> EngineKind + Wiper -> FrontWiper + Cabriolet -> RoofControl +  RainSensorWiper -> RainSensor]
	Combined/FeatureModel/Alternative[Chassis -> (StationWagon + Cabriolet) + AirConditioner -> (ClimateControl + ManualControl) + GearBox -> (AutoGearBox + ManualGearBox) + FrontWiper -> (RainSensorWiper + IntervalWiper) + RoofControl -> (ManualRoofControl + AutoRoofControl) + EngineKind -> (Gasoline + Diesel + Hybrid + Electric) + EngineSize -> (_4Cylinders + _6Cylinders + _8Cylinders)]
	Combined/FeatureModel/Optional[Automobile -> AirConditioner + GearBox -> _4x4GearBox + Engine -> EngineSize + Wiper -> RearWiper]
	Combined/FeatureModel/Or[EnergyReservoir -> (Accumulator + GasolineTank)]
	Combined/FeatureModel/Requires[StationWagon->RearWiper + (Electric + Hybrid) -> Accumulator + (Gasoline + Diesel + Hybrid) -> (GasolineTank + EngineSize) + AutoRoofControl -> RainSensor + _8Cylinders -> AutoGearBox + _4Cylinders -> ManualGearBox + Hybrid -> (_4Cylinders + AutoGearBox)]
	Combined/FeatureModel/NoExcludes
}

fact {
	//Combined/ConvertFeatureModel
}

run {} for exactly 20 Configuration
