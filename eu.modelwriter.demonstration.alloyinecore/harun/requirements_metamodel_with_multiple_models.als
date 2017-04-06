open util/relation
open util/ordering[Model] as models

sig Model {
	has: set Requirement,

	requires: Requirement -> Requirement,
	refines: Requirement -> Requirement,
	contains: Requirement -> Requirement,
	partiallyRefines: Requirement -> Requirement,
	conflicts: Requirement -> Requirement,
	equals: Requirement -> Requirement
}

sig Requirement {

}

lone sig PR1_AirConditioning extends Requirement { }
lone sig PR2_ClimateControl extends Requirement { }
//one sig PR3_ extends Requirement { }
lone sig PR4_GearBox extends Requirement { }
lone sig PR5_ManualGear extends Requirement { }
lone sig PR6_AutomaticGear extends Requirement { }
//one sig PR7_ extends Requirement { }
lone sig PR8_Engine extends Requirement { }
//one sig PR9_ extends Requirement { }
//one sig PR10_ extends Requirement { }
lone sig PR11_ElectricEngine extends Requirement { }
lone sig PR12_HybridEngine extends Requirement { }
lone sig PR13_4Cylinder extends Requirement { }
//one sig PR14_ extends Requirement { }
lone sig PR15_CylinderEngine extends Requirement { }
lone sig PR16_EnergyReservoir extends Requirement { }
lone sig PR17_Accumulator extends Requirement { }
//one sig PR18_ extends Requirement { }
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

fact { let m0 = models/first | m0.has = Requirement }

// Preds begin
pred functional_facts[m:Model]{
	no m.requires & m.refines
	no m.requires & m.contains
	no m.requires & m.partiallyRefines
	no m.requires & m.conflicts
	no m.requires & m.equals

	no m.refines & m.contains
	no m.refines & m.partiallyRefines
	no m.refines & m.conflicts
	no m.refines & m.equals

	no m.contains & m.partiallyRefines
	no m.contains & m.conflicts
	no m.contains & m.equals

	no m.partiallyRefines & m.conflicts
	no m.partiallyRefines & m.equals

	no m.conflicts & m.equals

	no m.requires & ~(m.refines)
	no m.requires & ~(m.contains)
	no m.requires & ~(m.partiallyRefines)
	no m.requires & ~(m.conflicts)
	no m.requires & ~(m.equals)

	no m.refines & ~(m.contains)
	no m.refines & ~(m.partiallyRefines)
	no m.refines & ~(m.conflicts)
	no m.refines & ~(m.equals)

	no m.contains & ~(m.partiallyRefines)
	no m.contains & ~(m.conflicts)
	no m.contains & ~(m.equals)

	no m.partiallyRefines & ~(m.conflicts)
	no m.partiallyRefines & ~(m.equals)

	no m.conflicts & ~(m.equals)
}

pred equals_facts[m:Model] {
	all a,b: m.has {
		b in a.(m.equals) => a.(m.conflicts) = b.(m.conflicts)
		b in a.(m.equals) => a.(m.requires) = b.(m.requires)
		b in a.(m.equals) => a.(m.equals) = b.(m.equals)
		b in a.(m.equals) => a.(m.refines) = b.(m.refines)
		b in a.(m.equals) => a.(m.partiallyRefines) = b.(m.partiallyRefines)
		b in a.(m.equals) => a.(m.contains) = b.(m.contains)

		b in a.(m.equals) => a.~(m.conflicts) = b.~(m.conflicts)
		b in a.(m.equals) => a.~(m.requires) = b.~(m.requires)
		b in a.(m.equals) => a.~(m.equals) = b.~(m.equals)
		b in a.(m.equals) => a.~(m.refines) = b.~(m.refines)
		b in a.(m.equals) => a.~(m.partiallyRefines) = b.~(m.partiallyRefines)
		b in a.(m.equals) => a.~(m.contains) = b.~(m.contains)
	}
}

pred req_ref_facts[m:Model] {
	all a,b,c: m.has {
		b in a.(m.requires) && c in b.(m.refines) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.refines) && c in b.(m.requires) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.requires) && c in b.(m.contains) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.contains) && c in a.(m.requires) &&  c !in a.(m.contains) => c in a.(m.requires)
		b in a.(m.contains) && c in b.(m.refines) && c !in a.(m.contains) + a.(m.refines) + a.(m.partiallyRefines) => c in a.(m.requires)
	}
}

pred ref_cont_facts[m:Model] {
	all a,b,c: m.has {
		b in a.(m.refines) && c in b.(m.contains) => c in a.(m.refines)
		b in a.(m.partiallyRefines) && c in b.(m.contains) => c in a.(m.partiallyRefines)
		b in a.(m.refines) && c in b.(m.partiallyRefines) => c in a.(m.partiallyRefines)
		b in a.(m.partiallyRefines) && c in b.(m.refines) => c in a.(m.partiallyRefines)
	}
}

pred req_conf_facts[m:Model] {
	all a,b,c: m.has {
		b in a.(m.requires) && c in b.(m.conflicts) => c in a.(m.conflicts)
		b in a.(m.refines) && c in b.(m.conflicts) => c in a.(m.conflicts)
	}
}

pred relation_facts[m,m' : Model] {
	all a,c: m'.has {
		c in a.(m'.requires) => c in a.*(m'.equals).*(m.requires).*(m.contains).*(m.refines).*(m.contains).*(m.requires).*(m'.equals)
		c in a.(m'.refines) => c in a.*(m'.equals).*(m.requires).*(m.refines).*(m.requires).*(m.contains).*(m'.equals)
		c in a.(m'.equals) => c in a.*(m.equals).*(~(m.equals)).*(m.equals)
		c in a.(m'.contains) => c in a.*(m'.equals).*(m.contains).*(m'.equals)
		c in a.(m'.partiallyRefines) => c in a.*(m'.equals).*(m.refines).*(m.partiallyRefines).*(m.refines).*(m.contains).*(m'.equals)
		c in a.(m'.conflicts) => 	c in a.*(m'.equals).*(m.requires).*(m.refines).*(m.requires).(m.conflicts).*(m'.equals) 	|| 
												c in a.*(m'.equals).*(m.requires).*(m.refines).*(m.requires).~(m.conflicts).*(m'.equals) ||
										 		c in a.*(m'.equals).(m.conflicts).*~(m.requires).*(~(m.refines)).*(~(m.requires)).*(m'.equals) || 
												c in a.*(m'.equals).~(m.conflicts).*~(m.requires).*(~(m.refines)).*(~(m.requires)).*(m'.equals) 
	}
}

pred func_definitions[m:Model] {
	irreflexive[m.requires]
	antisymmetric[m.requires]
	transitive[m.requires]

	irreflexive[m.refines]
	antisymmetric[m.refines]
	transitive[m.refines]

	irreflexive[m.contains]
	antisymmetric[m.contains]
	transitive[m.contains]

	irreflexive[m.partiallyRefines]
	antisymmetric[m.partiallyRefines]
	transitive[m.partiallyRefines]

	irreflexive[m.conflicts]
	symmetric[m.conflicts]

	reflexive[m.equals, Requirement] // Makalede non-reflexive denmiş ama mantıken yanlış ve uygulamasında sonuç vermiyor.
	symmetric[m.equals]
	transitive[m.equals]
}

pred generateSolution {
	all m0:Model, m1: models/next[m0] {
		m0.has in m1.has

		m0.requires in m1.requires
		m0.refines in m1.refines
		m0.contains in m1.contains
		m0.partiallyRefines in m1.partiallyRefines
		m0.conflicts in m1.conflicts
		m0.equals in m1.equals

		func_definitions[m1]
		req_conf_facts[m1]
		ref_cont_facts[m1]
		req_ref_facts[m1]
		equals_facts[m1]
		functional_facts[m1]
		relation_facts[m0,m1]
	}
}
// Preds end

pred figure3 { 
	let m0 = models/first {
		Requirement = PR11_ElectricEngine + PR17_Accumulator + PR16_EnergyReservoir

		m0.requires = PR11_ElectricEngine -> PR17_Accumulator
		m0.refines = PR17_Accumulator -> PR16_EnergyReservoir
		no m0.partiallyRefines
		no m0.equals
		no m0.contains
		no m0.conflicts
	}
	generateSolution
}

pred figure4 { 
	let m0 = models/first {
		Requirement = PR1_AirConditioning + PR2_ClimateControl
		
		m0.requires = PR1_AirConditioning -> PR2_ClimateControl
		m0.refines = PR2_ClimateControl -> PR1_AirConditioning
		no m0.partiallyRefines
		no m0.equals
		no m0.contains
		no m0.conflicts
	}
	generateSolution
}

pred figure7 { 
	let m0 = models/first {
		Requirement = PR19_Chassis + PR20_StaticWagon + PR21_Cabriolet + PR22_RoofControl + PR23_ManualControl + PR24_SensorControl + PR25_Wiper + PR26_RearWiper + PR27_FrontWiper + PR28_FrontIntervalWiper + PR29_FrontRainSensorWiper + PR30_RainSensor
		
		m0.requires = PR19_Chassis -> PR25_Wiper + PR20_StaticWagon -> PR26_RearWiper + PR21_Cabriolet -> PR22_RoofControl + PR24_SensorControl -> PR30_RainSensor + PR29_FrontRainSensorWiper ->  PR30_RainSensor
		m0.refines = PR21_Cabriolet -> PR19_Chassis + PR20_StaticWagon -> PR19_Chassis + PR26_RearWiper -> PR25_Wiper + PR27_FrontWiper -> PR25_Wiper + PR28_FrontIntervalWiper -> PR27_FrontWiper + PR29_FrontRainSensorWiper -> PR27_FrontWiper + PR23_ManualControl -> PR22_RoofControl + PR24_SensorControl -> PR22_RoofControl  
		m0.conflicts = PR20_StaticWagon -> PR21_Cabriolet + PR23_ManualControl -> PR24_SensorControl + PR28_FrontIntervalWiper -> PR29_FrontRainSensorWiper
		no m0.partiallyRefines
		no m0.equals
		no m0.contains
	}
	generateSolution
}

pred figure8 { 
	let m0 = models/first {
		Requirement = PR5_ManualGear + PR6_AutomaticGear + PR15_CylinderEngine
		
		m0.requires = PR15_CylinderEngine -> PR6_AutomaticGear
		m0.conflicts = PR6_AutomaticGear -> PR5_ManualGear
		no m0.partiallyRefines
		no m0.equals
		no m0.contains
		no m0.refines
	}
	generateSolution
}

pred figure9 { 
	let m0 = models/first {
		Requirement = PR5_ManualGear + PR6_AutomaticGear + PR4_GearBox + PR8_Engine + PR12_HybridEngine + PR13_4Cylinder

		m0.requires = PR13_4Cylinder -> PR5_ManualGear + PR12_HybridEngine -> PR13_4Cylinder + PR12_HybridEngine -> PR6_AutomaticGear
		m0.refines = PR12_HybridEngine -> PR8_Engine + PR13_4Cylinder -> PR8_Engine + PR5_ManualGear -> PR4_GearBox + PR6_AutomaticGear -> PR4_GearBox 
		m0.conflicts = PR6_AutomaticGear -> PR5_ManualGear
		no m0.partiallyRefines
		no m0.equals
		no m0.contains
	}
	generateSolution
}

pred figure13 { 
	let m0 = models/first {
		Requirement = PR20_StaticWagon + PR26_RearWiper + PR25_Wiper + PR5_ManualGear

		m0.contains= PR20_StaticWagon -> PR26_RearWiper + PR20_StaticWagon -> PR25_Wiper
		m0.refines = PR26_RearWiper -> PR5_ManualGear + PR5_ManualGear -> PR25_Wiper
		no m0.partiallyRefines
		no m0.equals
		no m0.requires
		no m0.conflicts
	}
	generateSolution
}

pred figure15 { 
	let m0 = models/first {
		Requirement = PR20_StaticWagon + PR26_RearWiper + PR25_Wiper

		m0.requires = PR20_StaticWagon -> PR26_RearWiper
		m0.refines = PR26_RearWiper -> PR25_Wiper
		no m0.partiallyRefines
		no m0.equals
		no m0.contains
		no m0.conflicts
	}
	generateSolution
}


pred deneme { 
	let m0 = models/first {
		Requirement = PR20_StaticWagon + PR26_RearWiper + PR25_Wiper

		m0.contains = PR20_StaticWagon -> PR26_RearWiper
		m0.refines = PR26_RearWiper -> PR25_Wiper
		no m0.partiallyRefines
		no m0.equals
		no m0.requires
		no m0.conflicts
	}
	generateSolution
}

run figure3 for exactly 3 Requirement, 2 Model
run figure4 for exactly 2 Requirement, 2 Model // Sonuç vermemeli
run figure7 for exactly 12 Requirement, 2 Model
run figure8 for exactly 3 Requirement, 2 Model
run figure9 for exactly 6 Requirement, 2 Model // Sonuç vermemeli
run figure13 for exactly 4 Requirement, 2 Model
run figure15 for exactly 3 Requirement, 2 Model
run deneme for exactly 3 Requirement, 2 Model





