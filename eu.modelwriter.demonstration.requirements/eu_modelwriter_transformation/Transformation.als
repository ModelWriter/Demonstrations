module eu_modelwriter_transformation/Transformation

open eu_modelwriter_transformation_models/Clafer
open eu_modelwriter_transformation_models/Ecore
open eu_modelwriter_transformation/Type

//QVT-R incele
sig Mapping extends Element {
	EClass2Clafer: EClass one -> one (Clafer - ClaferModel),
}
fact {
	all e: EClass, c: Clafer, m: Mapping |  e -> c in m.EClass2Clafer => e.name = c.name
}

pred example { #Mapping >= 1 and #Clafer >2}
run example for  14 Element
