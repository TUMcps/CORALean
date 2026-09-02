import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.ConPolyZono.Float.Operations.API
import CORALean.ContSet.ConPolyZono.Float.Theorems.API
import CORALean.ContSet.ConPolyZono.Float.Instances

/-!
# Constrained polynomial zonotopes over a floating-point scalar, collected

The representation and its error box in `ConPolyZono`, the operations in
`Operations`, their guarantees in `Theorems`, and the operation instances in
`Instances` — the `InflatedContSet` one is in `ConPolyZono`, being what the
error box means.

The representation's docstring is where to read why the list of operations stops
where it does: `and`, the operation this representation exists for, computes new
constraint data, and an equality constraint admits no rounding in either
direction.
-/
