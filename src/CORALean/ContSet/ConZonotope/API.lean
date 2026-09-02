import CORALean.ContSet.ConZonotope.ConZonotope
import CORALean.ContSet.ConZonotope.Operations.API
import CORALean.ContSet.ConZonotope.Theorems.API
import CORALean.ContSet.ConZonotope.Instances

/-!
# Constrained zonotopes, collected

A zonotope whose coefficients are cut down by a polytope, so the two earlier
representations are both prerequisites: `Zonotope` for what is enclosed and
mapped, `HPolytope` for what the coefficients range over.

What it buys over a zonotope is `and`: intersection, exactly, which no zonotope
can represent.

The specification only. A float layer would pay two different roundings in two
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
