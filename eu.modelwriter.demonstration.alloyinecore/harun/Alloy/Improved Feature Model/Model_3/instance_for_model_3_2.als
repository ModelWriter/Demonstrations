open combined_feature_model as Combined

one sig MobilePhone extends Feature {}
one sig Calls extends Feature {}
one sig GPS extends Feature {}
one sig Screen extends Feature{}
one sig Media extends Feature {}
one sig Basic extends Feature {}
one sig Colour extends Feature {}
one sig HighResolution extends Feature {}
one sig Camera extends Feature {}
one sig MP3 extends Feature {}
one sig Deneme extends Feature {}


fact init_feature_model {
	Combined/FeatureModel/Root[MobilePhone]

	Combined/FeatureModel/Mandatory[MobilePhone -> (Calls + Screen) + GPS -> Deneme]
	Combined/FeatureModel/Alternative[Screen -> (Basic + Colour + HighResolution)]
	Combined/FeatureModel/Optional[MobilePhone -> (GPS + Media)]
	Combined/FeatureModel/Or[Media -> (Camera + MP3)]
	Combined/FeatureModel/Requires[Camera -> HighResolution]
	Combined/FeatureModel/Excludes[Basic -> GPS + Colour -> Deneme]
}

fact {
	Combined/ConvertFeatureModel
}

run {} for exactly 4 Configuration
