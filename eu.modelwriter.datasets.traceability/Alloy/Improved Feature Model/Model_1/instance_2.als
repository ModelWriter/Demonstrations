open feature_model[Feature] as FeatureModel

abstract sig Feature {}

one sig F1 extends Feature {}
one sig F2 extends Feature {}
one sig F3 extends Feature {}
one sig F4 extends Feature {}

fact init_feature_model {
	FeatureModel/Root[F1]

	FeatureModel/Mandatory[F1 -> (F3 + F4)]
	FeatureModel/Optional[F1 -> F2]
	FeatureModel/NoAlternative
	FeatureModel/NoOptionalOr
	FeatureModel/NoMandatoryOr
	FeatureModel/NoRequires
	FeatureModel/Excludes[F3->F2]
}

run {} for exactly 1 Instance
