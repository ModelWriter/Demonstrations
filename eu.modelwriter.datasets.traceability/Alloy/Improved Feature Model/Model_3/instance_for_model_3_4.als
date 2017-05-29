open combined_feature_model as Combined

one sig A extends Feature {}
one sig B extends Feature {}
one sig C extends Feature {}
one sig D extends Feature{}
one sig E extends Feature{}

fact init_feature_model {
	Combined/FeatureModel/Root[A]

	Combined/FeatureModel/NoMandatory
/*
	Combined/FeatureModel/NoAlternative
	Combined/FeatureModel/Optional[B -> D]
*/
	Combined/FeatureModel/Alternative[B -> (D + E)]
	Combined/FeatureModel/NoOptional
	Combined/FeatureModel/Or[A -> (B + C)]
	Combined/FeatureModel/NoRequires
	Combined/FeatureModel/Excludes[B -> C]
}

fact {
	Combined/ConvertFeatureModel
}

run {} for exactly 3 Configuration
