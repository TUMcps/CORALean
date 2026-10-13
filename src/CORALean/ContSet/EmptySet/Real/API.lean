module

public import CORALean.ContSet.EmptySet.Real.EmptySet
public import CORALean.ContSet.EmptySet.Real.Instances
public import CORALean.ContSet.EmptySet.Real.Operations.API
public import CORALean.ContSet.EmptySet.Real.Theorems.API

/-!
# The empty set, collected

The representation in `EmptySet`, the class instances in `Instances`, CORA's
dimension-changing and conversion methods in `Operations/` and what each guarantees in
`Theorems/`.

The class instances carry the proofs of the interface's inclusions, a line each: there is
one value of `EmptySet n` and one set it denotes. What does not fit an interface class
(`project`, `lift_`, `not`, the conversions) is a definition in `Operations/` with an
equality in `Theorems/`.
-/
