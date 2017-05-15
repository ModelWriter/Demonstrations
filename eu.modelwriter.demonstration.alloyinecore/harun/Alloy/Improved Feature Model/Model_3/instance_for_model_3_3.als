open combined_feature_model as Combined

one sig Car extends Feature {}
one sig Body extends Feature {}
one sig Transmission extends Feature {}
one sig PullsTrailer extends Feature {}
one sig Engine extends Feature {}
one sig Automatic extends Feature {}
one sig Manual extends Feature {}
one sig Gasoline extends Feature {}
one sig Electric extends Feature {}


fact init_feature_model {
	Combined/FeatureModel/Root[Car]

	Combined/FeatureModel/Mandatory[Car -> (Body + Transmission + Engine)]
	Combined/FeatureModel/Alternative[Transmission -> (Automatic + Manual)]
	Combined/FeatureModel/Optional[Car -> PullsTrailer]
	Combined/FeatureModel/Or[Engine-> (Gasoline + Electric)]
	Combined/FeatureModel/NoRequires
	Combined/FeatureModel/NoExcludes
}

fact conversion {
	Combined/ConvertFeatureModel
}

run {} for exactly 12 Configuration
