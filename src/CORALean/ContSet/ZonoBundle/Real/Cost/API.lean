import CORALean.ContSet.ZonoBundle.Real.Cost.Plus
import CORALean.ContSet.ZonoBundle.Real.Cost.Mtimes
import CORALean.ContSet.ZonoBundle.Real.Cost.LinComb
import CORALean.ContSet.ZonoBundle.Real.Cost.And
import CORALean.ContSet.ZonoBundle.Real.Cost.Reduce

/-!
# What running `ZonoBundle`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one of them **asserted**. `Complexity/` is the other directory
and the other kind of claim: how large a *result* is, which is proved.

Every operation here is its `Zonotope` counterpart run over the members, so
every count is the zonotope count times a member count and this directory adds
no arithmetic of its own. Two shapes come out of that: `plus` and `linComb` pair
the members and pay `k₁ * k₂`, while `mtimes` walks one family and pays `k`.

`and` and `reduce` cost nothing — concatenation and truncation — which is the
bargain the representation is built on and what makes the member count the thing
to watch. `map` and `mtimesMatZonotope` are left out: `Zonotope/Real/Cost/`
prices neither, and a bundle's count cannot be tighter than its member's.

A generator count here bounds *every* member rather than naming one, since the
structure carries a family and no common width.
-/
