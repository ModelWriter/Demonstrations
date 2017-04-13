module module_sysmlmodel[exactly Requirement]

open util/relation

abstract sig SysmlModel {
	deriveReqt: Requirement -> Requirement,
	refines: Requirement -> Requirement,
	composedBy: Requirement -> Requirement,
	copy: Requirement -> Requirement
}

one sig EmptySysmlModel, GivenSysmlModel extends SysmlModel {}

fact {
	func_definitions[GivenSysmlModel]
	NoRelations[EmptySysmlModel]
}

private pred func_definitions[m: SysmlModel] {
	no m.deriveReqt & m.refines
	no m.deriveReqt & m.composedBy
	no m.deriveReqt & m.copy

	no m.refines & m.composedBy
	no m.refines & m.copy
	
	no m.composedBy & m.copy

	no m.deriveReqt & ~(m.refines)
	no m.deriveReqt & ~(m.composedBy)
	no m.deriveReqt & ~(m.copy)

	no m.refines & ~(m.composedBy)
	no m.refines & ~(m.copy)
	
	no m.composedBy & ~(m.copy)

	irreflexive[m.deriveReqt]
	irreflexive[m.refines]
	irreflexive[m.composedBy]
	antisymmetric[m.deriveReqt]
	antisymmetric[m.refines]
	antisymmetric[m.composedBy]
}

pred NoRelations[m: SysmlModel] {
	no m.deriveReqt
	no m.refines
	no m.composedBy
	no m.copy
}

pred DeriveReqt[r1, r2: Requirement] {
	r1 -> r2 in GivenSysmlModel.deriveReqt
}

pred Refines[r1, r2: Requirement] {
	r1 -> r2 in GivenSysmlModel.refines
}

pred ComposedBy[r1, r2: Requirement] {
	r1 -> r2 in GivenSysmlModel.composedBy
}

pred Copy[r1, r2: Requirement] {
	r1 -> r2 in GivenSysmlModel.copy
}

pred DeriveReqt[r: Requirement -> Requirement] {
	r = GivenSysmlModel.deriveReqt
}

pred Refines[r: Requirement -> Requirement] {
	r = GivenSysmlModel.refines
}

pred ComposedBy[r: Requirement -> Requirement]  {
	r = GivenSysmlModel.composedBy
}

pred Copy[r: Requirement -> Requirement]  {
	r = GivenSysmlModel.copy
}

pred NoDeriveReqt {
	no GivenSysmlModel.deriveReqt
}

pred NoRefines {
	no GivenSysmlModel.refines
}

pred NoComposedBy {
	no GivenSysmlModel.composedBy
}

pred NoCopy {
	no GivenSysmlModel.copy
}






