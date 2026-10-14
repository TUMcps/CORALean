module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.API
public import CORALean.ContSet.PolyZonotope.Real.Theorems.API
public import CORALean.ContSet.PolyZonotope.Real.Counterexamples.API
public import CORALean.ContSet.PolyZonotope.Real.Complexity.API
public import CORALean.ContSet.PolyZonotope.Real.Instances

/-!
# Sparse polynomial zonotopes, collected

The representation in `PolyZonotope`, the operations in `Operations`, their
guarantees in `Theorems`, how large their results are in `Complexity/Space`, what running them
costs in `Complexity/Time`, and the class instances in `Instances`.

`Complexity/Space` is proved and `Complexity/Time` is asserted;
`Complexity/Time/API.lean` says why the two cannot be the same kind of claim.
-/
