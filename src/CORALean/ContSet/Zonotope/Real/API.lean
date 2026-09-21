import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Zonotope.Real.Aligned
import CORALean.ContSet.Zonotope.Real.AdaptSetOrder
import CORALean.ContSet.Zonotope.Real.EnclGenSel
import CORALean.ContSet.Zonotope.Real.AutoTuneSetOrder
import CORALean.ContSet.Zonotope.Real.ReduceBoxOrder
import CORALean.ContSet.Zonotope.Real.Operations.API
import CORALean.ContSet.Zonotope.Real.Theorems.API
import CORALean.ContSet.Zonotope.Real.Complexity.API
import CORALean.ContSet.Zonotope.Real.Cost.API
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# Zonotopes, collected

The representation in `Zonotope`, when two of them count as aligned in
`Aligned`, the operations in `Operations`, their
guarantees in `Theorems`, how large their results are in `Complexity`, what
running them costs in `Cost`, and the class instances in `Instances`.

`Complexity` is proved and `Cost` is asserted; `Cost/API.lean` says why the two
cannot be the same kind of claim.
-/
