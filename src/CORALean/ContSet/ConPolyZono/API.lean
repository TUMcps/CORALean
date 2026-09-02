import CORALean.ContSet.ConPolyZono.Real.API
import CORALean.ContSet.ConPolyZono.Float.API

/-!
# Constrained polynomial zonotopes

Kochdumper and Althoff (2020), and CORA's `conPolyZono`: a polynomial zonotope
whose factors additionally satisfy polynomial equalities, over the very same
factors the generators use.

What it buys over a polynomial zonotope is `and`: intersection, exactly, of sets
that need not be convex. `ConZonotope` buys the same operation for zonotopes,
and the two are the only representations here that intersect without loss.

The float layer carries `plus` and `mtimes` and stops there. `and` is where a
constrained representation meets a limit no other one here does: an equality
constraint has no direction to round in, so an operation that computes new
constraint data — and `and`'s right-hand side is `c₂ - c₁` — can be refined only
once the exact layer admits a slack factor or an interval right-hand side.
Neither is faked.
-/
