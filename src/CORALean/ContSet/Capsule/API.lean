import CORALean.ContSet.Capsule.Real.API

/-!
# Capsules

CORA's `capsule`: a segment thickened by a Euclidean ball, `{c + t g | t ∈
[-1, 1]} ⊕ ball(0, r)`. CORA uses it to describe an obstacle, not to carry a
reachable set through an operation — `Instances.lean` says why almost nothing
is closed under it.

Real layer only: nothing here rounds, so a float layer would only ever widen a
real capsule's radius, which every existing conversion already does through
`Interval`.
-/
