import CORALean.ContSet.ConPolyZono.Real.API

/-!
# Constrained polynomial zonotopes

Kochdumper and Althoff (2020), and CORA's `conPolyZono`: a polynomial zonotope
whose factors additionally satisfy polynomial equalities, over the very same
factors the generators use.

What it buys over a polynomial zonotope is `and`: intersection, exactly, of sets
that need not be convex. `ConZonotope` buys the same operation for zonotopes,
and the two are the only representations here that intersect without loss.

`Real` only so far; the float layer is not written.
-/
