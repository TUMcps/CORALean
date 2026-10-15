module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Operations.API
public import CORALean.ContSet.ConZonotope.Real.Theorems.API
public import CORALean.ContSet.ConZonotope.Real.Counterexamples.API
public import CORALean.ContSet.ConZonotope.Real.Complexity.API
public import CORALean.ContSet.ConZonotope.Real.Instances

/-!
# Constrained zonotopes, collected

A zonotope whose coefficients are cut down by a polytope, so the two earlier
representations are both prerequisites: `Zonotope` for what is enclosed and
mapped, `HPolytope` for what the coefficients range over. `Complexity/Space` sizes both
counts together, and `Complexity/Time` counts what running the three operations that build
no constraint costs — its own docstring says why the other three are left out.

What it buys over a zonotope is `intersection`, exactly, which no zonotope can
represent.

Both layers are specified. `Float` pays two different roundings in two
different places: the center and generators into an ambient error box, as the
float zonotope does, and the constraints into the polytope's rows, an equality that must be
rounded being written as two inequalities — `HPolytope` records why an ambient box cannot pay
for those. One error box, not two: the coefficient polytope is read at its nominal part, and
its own box is not.

The general rule the two cases share: pay rounding where the representation
already has slack of the same kind. An interval's bounds are slack, and a
constraint's are; a zonotope's generators are not, since paying into them grows
the order at every operation.
-/
