import CORALean.ContSet.ConZonotope.ConZonotope
import CORALean.ContSet.ConZonotope.Operations.API
import CORALean.ContSet.ConZonotope.Theorems.API
import CORALean.ContSet.ConZonotope.Instances

/-!
# Constrained zonotopes, collected

A zonotope whose coefficients are cut down by a polytope, so the two earlier
representations are both prerequisites: `Zonotope` for what is enclosed and
mapped, `Polytope` for what the coefficients range over.

What it buys over a zonotope is `and`: intersection, exactly, which no zonotope
can represent.

The specification only. A float layer would pay its rounding into an error box,
as the zonotope's does, and would additionally have to round the constraints —
which cannot be done outward, an equality having no slack to give.
-/
