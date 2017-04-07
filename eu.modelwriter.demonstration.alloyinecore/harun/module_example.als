open module_requirementsmodel[Requirement] as Model

abstract sig Requirement {}

lone sig PR1_AirConditioning extends Requirement { }
lone sig PR2_ClimateControl extends Requirement { }
lone sig PR4_GearBox extends Requirement { }
lone sig PR5_ManualGear extends Requirement { }
lone sig PR6_AutomaticGear extends Requirement { }
lone sig PR8_Engine extends Requirement { }
lone sig PR11_ElectricEngine extends Requirement { }
lone sig PR12_HybridEngine extends Requirement { }
lone sig PR13_4Cylinder extends Requirement { }
lone sig PR15_CylinderEngine extends Requirement { }
lone sig PR16_EnergyReservoir extends Requirement { }
lone sig PR17_Accumulator extends Requirement { }
lone sig PR19_Chassis extends Requirement { }
lone sig PR20_StaticWagon extends Requirement { }
lone sig PR21_Cabriolet extends Requirement { }
lone sig PR22_RoofControl extends Requirement { }
lone sig PR23_ManualControl extends Requirement { }
lone sig PR24_SensorControl extends Requirement { }
lone sig PR25_Wiper extends Requirement { }
lone sig PR26_RearWiper extends Requirement { }
lone sig PR27_FrontWiper extends Requirement { }
lone sig PR28_FrontIntervalWiper extends Requirement { }
lone sig PR29_FrontRainSensorWiper extends Requirement { }
lone sig PR30_RainSensor extends Requirement { }

pred figure3 { 
	Requirement = PR11_ElectricEngine + PR17_Accumulator + PR16_EnergyReservoir

	Model/Requires[PR11_ElectricEngine -> PR17_Accumulator]
	Model/Refines[PR17_Accumulator -> PR16_EnergyReservoir]
	Model/NoPartiallyRefines
	Model/NoEquals
	Model/NoContains
	Model/NoConflicts
}

pred figure4 { 
	Requirement = PR1_AirConditioning + PR2_ClimateControl
		
	Model/Requires[PR1_AirConditioning -> PR2_ClimateControl]
	Model/Refines[PR2_ClimateControl -> PR1_AirConditioning]
	Model/NoPartiallyRefines
	Model/NoEquals
	Model/NoContains
	Model/NoConflicts
}

pred figure7 { 
	Requirement = PR19_Chassis + PR20_StaticWagon + PR21_Cabriolet + PR22_RoofControl + PR23_ManualControl + PR24_SensorControl + PR25_Wiper + PR26_RearWiper + PR27_FrontWiper + PR28_FrontIntervalWiper + PR29_FrontRainSensorWiper + PR30_RainSensor
		
	Model/Requires[PR19_Chassis -> PR25_Wiper + PR20_StaticWagon -> PR26_RearWiper + PR21_Cabriolet -> PR22_RoofControl + PR24_SensorControl -> PR30_RainSensor + PR29_FrontRainSensorWiper ->  PR30_RainSensor]
	Model/Refines[PR21_Cabriolet -> PR19_Chassis + PR20_StaticWagon -> PR19_Chassis + PR26_RearWiper -> PR25_Wiper + PR27_FrontWiper -> PR25_Wiper + PR28_FrontIntervalWiper -> PR27_FrontWiper + PR29_FrontRainSensorWiper -> PR27_FrontWiper + PR23_ManualControl -> PR22_RoofControl + PR24_SensorControl -> PR22_RoofControl]  
	Model/Conflicts[PR20_StaticWagon -> PR21_Cabriolet + PR23_ManualControl -> PR24_SensorControl + PR28_FrontIntervalWiper -> PR29_FrontRainSensorWiper]
	Model/NoPartiallyRefines
	Model/NoEquals
	Model/NoContains
}

pred figure8 { 
	Requirement = PR5_ManualGear + PR6_AutomaticGear + PR15_CylinderEngine
		
	Model/Requires[PR15_CylinderEngine -> PR6_AutomaticGear]
	Model/Conflicts[PR6_AutomaticGear -> PR5_ManualGear]
	Model/NoPartiallyRefines
	Model/NoEquals
	Model/NoContains
	Model/NoRefines
}

pred figure9 { 
	Requirement = PR5_ManualGear + PR6_AutomaticGear + PR4_GearBox + PR8_Engine + PR12_HybridEngine + PR13_4Cylinder

	Model/Requires[PR13_4Cylinder -> PR5_ManualGear + PR12_HybridEngine -> PR13_4Cylinder + PR12_HybridEngine -> PR6_AutomaticGear]
	Model/Refines[PR12_HybridEngine -> PR8_Engine + PR13_4Cylinder -> PR8_Engine + PR5_ManualGear -> PR4_GearBox + PR6_AutomaticGear -> PR4_GearBox]
	Model/Conflicts[PR6_AutomaticGear -> PR5_ManualGear]
	Model/NoPartiallyRefines
	Model/NoEquals
	Model/NoContains
}

pred figure13 { 
	Requirement = PR20_StaticWagon + PR26_RearWiper + PR25_Wiper + PR5_ManualGear

	Model/Contains[PR20_StaticWagon -> PR26_RearWiper + PR20_StaticWagon -> PR25_Wiper]
	Model/Refines[PR26_RearWiper -> PR5_ManualGear + PR5_ManualGear -> PR25_Wiper]
	Model/NoPartiallyRefines
	Model/NoEquals
	Model/NoRequires
	Model/NoConflicts
}

pred figure15 { 
	Requirement = PR20_StaticWagon + PR26_RearWiper + PR25_Wiper

	Model/Requires[PR20_StaticWagon -> PR26_RearWiper]
	Model/Refines[PR26_RearWiper -> PR25_Wiper]
	Model/NoPartiallyRefines
	Model/NoEquals
	Model/NoContains
	Model/NoConflicts
}

run figure3 for exactly 3 Requirement
run figure4 for exactly 2 Requirement // No Result
run figure7 for exactly 12 Requirement
run figure8 for exactly 3 Requirement
run figure9 for exactly 6 Requirement // No Result
run figure13 for exactly 4 Requirement
run figure15 for exactly 3 Requirement

