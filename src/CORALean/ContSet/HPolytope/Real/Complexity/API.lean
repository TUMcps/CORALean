import CORALean.ContSet.HPolytope.Real.Complexity.Intersection
import CORALean.ContSet.HPolytope.Real.Complexity.Mtimes
import CORALean.ContSet.HPolytope.Real.Complexity.MinkDiffOf

/-!
# What `HPolytope` costs

The size of an operation's result as a function of its operands' — the
inequality-row count `m` and the equality-row count `me`, since a halfspace
description carries both. Each theorem is `rfl` against the structure instance
in `Operations/`.

`mtimesOf`'s `m` restates `q`, the caller's own choice of how many directions
to bound, but `q` is not a type index the way `Interval`'s `n` is — it is a
field the operation computes, exactly as `Zonotope.reduceBy_h` restates its
caller-chosen `q` — so the equation is worth having, and `me = 0` is not
visible at the call site at all.

`comap` and `halfScaled` are not counted here: both leave `m` and `me`
untouched, by the same one-line argument each time, and neither is one of the
three operations #5 names.

No operation here multiplies, so there is no `O`-notation candidate in this
directory; `ConZonotope`'s constrained-zonotope operations are where an
`HPolytope`'s row count actually compounds.

The number of scalar operations each operation costs is not yet stated here.
-/
