import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.ConZonotope.Real.Operations.API
import CORALean.ContSet.ConZonotope.Real.Theorems.API
import CORALean.ContSet.ConZonotope.Real.Complexity.API
import CORALean.ContSet.ConZonotope.Real.Cost.API
import CORALean.ContSet.ConZonotope.Real.Instances

/-!
# Constrained zonotopes, collected

A zonotope whose coefficients are cut down by a polytope, so the two earlier
representations are both prerequisites: `Zonotope` for what is enclosed and
mapped, `HPolytope` for what the coefficients range over. `Complexity` sizes both
counts together, and `Cost` counts what running the three operations that build
no constraint costs — its own docstring says why the other three are left out.

What it buys over a zonotope is `and`: intersection, exactly, which no zonotope
can represent.

Both layers are specified. `Float` pays two different roundings in two
different places: the centre and generators into an ambient error box, as the
float zonotope does, and the constraints into the polytope itself, whose float
form carries an interval right-hand side — `HPolytope` records why an ambient box
cannot pay for those. One error box, not two, and no nested float polytope
carrying a box of its own.

The general rule the two cases share: pay rounding where the representation
already has slack of the same kind. An interval's bounds are slack, and a
constraint's are; a zonotope's generators are not, since paying into them grows
the order at every operation.
-/
