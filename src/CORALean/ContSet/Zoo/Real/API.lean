module

public import CORALean.ContSet.Zoo.Real.Zoo
public import CORALean.ContSet.Zoo.Real.Operations.API
public import CORALean.ContSet.Zoo.Real.Theorems.API

/-!
# Zoos, collected

The representation in `Zoo`, the operations in `Operations` and their guarantees in
`Theorems`. A zoo encloses a function, not a point: its `ContSet` instance is over
functions, the `SetIntersection` of its members.
-/
