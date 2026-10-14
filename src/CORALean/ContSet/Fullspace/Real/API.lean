module

public import CORALean.ContSet.Fullspace.Real.Counterexamples.API
public import CORALean.ContSet.Fullspace.Real.Fullspace
public import CORALean.ContSet.Fullspace.Real.Instances
public import CORALean.ContSet.Fullspace.Real.Operations.API
public import CORALean.ContSet.Fullspace.Real.Theorems.API

/-!
# The full space, collected

The representation in `Fullspace`, the class instances in `Instances`, CORA's
dimension-changing and conversion methods in `Operations/` and what each guarantees in
`Theorems/`.

There is one value of `Fullspace n`, so every operation returns it and the interface
instances say so in a line each; what does not fit an interface class (`project`,
`lift_`, `not`, the conversions) is a definition in `Operations/` with an equality in
`Theorems/`.
-/
