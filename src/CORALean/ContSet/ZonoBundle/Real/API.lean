module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.ZonoBundle.Real.Operations.API
public import CORALean.ContSet.ZonoBundle.Real.Theorems.API
public import CORALean.ContSet.ZonoBundle.Real.Complexity.API
public import CORALean.ContSet.ZonoBundle.Real.Instances

/-!
# Zonotope bundles, collected

The representation in `ZonoBundle`, the operations in `Operations`, their
guarantees in `Theorems`, how large their results are in `Complexity/Space`, what running them
costs in `Complexity/Time`, and the class instances in `Instances`.

`Complexity/Space` is proved and `Complexity/Time` is asserted;
`Complexity/Time/API.lean` says why the two cannot be the same kind of claim.
-/
