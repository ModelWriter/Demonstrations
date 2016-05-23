module eu_modelwriter_transformation/Type

/*Type Module*/
abstract sig Element {}
sig string extends Element {}
abstract sig boolean extends Element {}
one sig false,true extends boolean {}
--sig integer extends Element {}
