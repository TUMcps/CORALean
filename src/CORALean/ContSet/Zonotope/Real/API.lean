import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Zonotope.Real.Definitions.API
import CORALean.ContSet.Zonotope.Real.Operations.API
import CORALean.ContSet.Zonotope.Real.Theorems.API
import CORALean.ContSet.Zonotope.Real.Complexity.API
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# Zonotopes, collected

The representation in `Zonotope`, what two of them being aligned means in
`Definitions`, the operations in `Operations`, their guarantees in `Theorems`,
how large their results are in `Complexity/Space`, what running them
costs in `Complexity/Time`, and the class instances in `Instances`.

`Complexity/Space` is proved and `Complexity/Time` is asserted;
`Complexity/Time/API.lean` says why the two cannot be the same kind of claim.
-/
