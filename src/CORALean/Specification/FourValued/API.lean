module

public import CORALean.Specification.FourValued.FourValued
public import CORALean.Specification.FourValued.Instances
public import CORALean.Specification.FourValued.Operations.API
public import CORALean.Specification.FourValued.Theorems.API

/-!
# Four-valued logic, collected

CORA's `fourValued`: `FourValued` the four members, `Operations` the five methods, `Theorems` the
laws they satisfy (lattice, De Morgan, absorption, distributivity) and that `fromKleene`
is a homomorphism of `&`, `|` and `~`.
-/
