import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.ZonoBundle.Real.Operations.API
import CORALean.ContSet.ZonoBundle.Real.Theorems.API
import CORALean.ContSet.ZonoBundle.Real.Complexity.API
import CORALean.ContSet.ZonoBundle.Real.Cost.API
import CORALean.ContSet.ZonoBundle.Real.Instances

/-!
# Zonotope bundles, collected

The representation in `ZonoBundle`, the operations in `Operations`, their
guarantees in `Theorems`, how large their results are in `Complexity`, what
running them costs in `Cost`, and the class instances in `Instances`.

`Complexity` is proved and `Cost` is asserted; `Cost/API.lean` says why the two
cannot be the same kind of claim.
-/
