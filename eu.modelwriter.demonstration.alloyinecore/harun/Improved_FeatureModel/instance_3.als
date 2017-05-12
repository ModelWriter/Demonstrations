open feature_model[Feature] as FeatureModel

abstract sig Feature {}

one sig F1 extends Feature {}
one sig F2 extends Feature {}
one sig F3 extends Feature {}
one sig F4 extends Feature {}
one sig F5 extends Feature {}
one sig F6 extends Feature {}
one sig F7 extends Feature {}

fact init_feature_model {
	FeatureModel/Root[F1]

	FeatureModel/NoMandatory
	FeatureModel/NoOptional
	FeatureModel/Alternative[F1 -> (F2 + F3) + F2 -> (F4 + F5) + F3 -> (F6 + F7)]
	FeatureModel/NoOptionalOr
	FeatureModel/NoMandatoryOr
	FeatureModel/NoRequires
	FeatureModel/NoExcludes
}

// Let's define our instance and check if the selection is possible

one sig MyInstance extends FeatureModel/Instance {}

pred define_1 {
	MyInstance.includes = F1 + F2 + F5 // Possible
}

pred define_2 {
	MyInstance.includes = F1 + F2 + F6 // Not possible
}

run define_1 for exactly 1 Instance

run define_2 for exactly 1 Instance
