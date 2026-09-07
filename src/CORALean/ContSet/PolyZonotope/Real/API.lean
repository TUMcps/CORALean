import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.API
import CORALean.ContSet.PolyZonotope.Real.Theorems.API
import CORALean.ContSet.PolyZonotope.Real.Complexity.API
import CORALean.ContSet.PolyZonotope.Real.Cost.API
import CORALean.ContSet.PolyZonotope.Real.Instances

/-!
# Sparse polynomial zonotopes, collected

The representation in `PolyZonotope`, the operations in `Operations`, their
guarantees in `Theorems`, how large their results are in `Complexity`, what
running them costs in `Cost`, and the class instances in `Instances`.

`Complexity` is proved and `Cost` is asserted; `Cost/API.lean` says why the two
cannot be the same kind of claim.
-/
