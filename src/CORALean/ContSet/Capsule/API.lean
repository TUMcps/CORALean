module

public import CORALean.ContSet.Capsule.Real.API
public import CORALean.ContSet.Capsule.Float.API

/-!
# Capsules

CORA's `capsule`: a segment thickened by a Euclidean ball, `{c + t g | t ∈
[-1, 1]} ⊕ ball(0, r)`. CORA uses it to describe an obstacle, not to carry a
reachable set through an operation — `Instances.lean` says why almost nothing
is closed under it.

Over ℝ and over a floating-point scalar. The float layer stores the same three fields in `𝕋`
and rounds only where it must: `Capsule.interval`, the bounding box every conversion goes
through, rounds its bounds outward.
-/
