module

public import CORALean.ContSet.ConPolyZono.Real.API
public import CORALean.ContSet.ConPolyZono.Float.API

/-!
# Constrained polynomial zonotopes

CORA's `conPolyZono` [1]: a polynomial zonotope whose factors additionally
satisfy polynomial constraints, over the very same factors the generators use.

What it buys over a polynomial zonotope is `intersection`, exactly, of sets that
need not be convex. `ConZonotope` buys the same operation for zonotopes;
with `ZonoBundle`, the three are the only representations here that intersect
without loss.

The constraint is [1, Def. 5]'s, `A μ_R(α) = b` with `b` a vector: a polynomial level set on the
factors with `=` in every row (`ConPolyZono.cons`). An equation has no direction to be rounded
in, so the float layer records each row's rounding beside it, as a slack `b_error`, and its
nominal set is the exact one with a slack factor per row (`ConPolyZono.relax`) — which is what
carries `intersection` across to the float layer, and what lets a `ConZonotope`, inequalities
and all, convert in exactly. As a star set its predicate is that level set
(`ConPolyZono.starSet`).

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/
