import CORALean.ContSet.HPolytope.Float.Operations.And
import CORALean.ContSet.HPolytope.Float.Operations.Pad
import CORALean.ContSet.HPolytope.Float.Operations.OfMat

/-!
# What the float `HPolytope` computes

All of it exactly. `and` concatenates constraint lists, `padLeft` and `padRight`
widen the coefficient space with zeros, and the two constructors copy matrices —
none of them performs an arithmetic operation, so none of them rounds.

Rounding reaches a halfspace description only through the data handed to it,
which is why `be` is an interval and no operation here needs an error box.
-/
