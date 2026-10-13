module

public import CORALean.ContSet.ZonoBundle.Real.Complexity.Time.Plus
public import CORALean.ContSet.ZonoBundle.Real.Complexity.Time.Mtimes
public import CORALean.ContSet.ZonoBundle.Real.Complexity.Time.Map
public import CORALean.ContSet.ZonoBundle.Real.Complexity.Time.LinComb
public import CORALean.ContSet.ZonoBundle.Real.Complexity.Time.Intersection
public import CORALean.ContSet.ZonoBundle.Real.Complexity.Time.Reduce

/-!
# What running `ZonoBundle`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one of them **asserted**. `Complexity/Space/` is the other directory
and the other kind of claim: how large a *result* is, which is proved.

Every operation here is its `Zonotope` counterpart run over the members, so
every count is the zonotope count times a member count and this directory adds
no arithmetic of its own. Two shapes come out of that: `plus` and `linComb` pair
the members and pay `k₁ * k₂`, while `mtimes` walks one family and pays `k`.

`intersection` and `reduce` cost nothing — concatenation and truncation — which is the
bargain the representation is built on and what makes the member count the thing
to watch. `mapCost` prices a general map at what one application costs, run
over every member, the same parameter `Zonotope.mapCost` takes. `mtimesMatZonotope`
is left out: `Zonotope/Real/Complexity/Time/` does not price it either.

A generator count here bounds *every* member rather than naming one, since the
structure carries a family and no common width.
-/
