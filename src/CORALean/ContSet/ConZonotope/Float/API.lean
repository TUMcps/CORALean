import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.ConZonotope.Float.Operations.API
import CORALean.ContSet.ConZonotope.Float.Theorems.API
import CORALean.ContSet.ConZonotope.Float.Instances

/-!
# Constrained zonotopes over a floating-point scalar, collected

Two roundings in two places: the centre and generators into the ambient error
box, the constraints into `P`, whose float form carries an interval right-hand
side. One box, not two.

`mtimes` and `and` are still missing. Both are reachable, and both want the same
thing first: the float zonotope's `mtimes` argument stated about the
*coefficients* rather than about the set, so a representation carrying extra
conditions on them can reuse it instead of repeating thirty-five lines. `and`
additionally needs its agreement rows widened by `E₂ ⊖ E₁`, which is exactly what
an interval right-hand side is for — the two incoming boxes displace the point
the rows pin together.
-/
