import CORALean.ContSet.Capsule.Real.Operations.SegDist

/-!
# `Capsule.isIntersecting_`

CORA's `@capsule/isIntersecting_.m` for two capsules, `aux_isIntersecting_capsule`: the axes are
at most the sum of the radii apart (`dist < r₁ + r₂ | withinTol(dist, r₁ + r₂)`, `dist ≤ r₁ + r₂`
at tolerance `0`). The emptiness test CORA runs first never sees a negative radius
(`isempty(C.r)` only), so, unlike `construct`, this test does not read `r < 0` as `∅`. The point,
hyperplane and generic operand types are not modelled.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_isIntersecting_capsule(C₁, C₂)` at tolerance `0`. -/
noncomputable def Capsule.isIntersecting_ (C₁ C₂ : Capsule n) : Prop :=
  let dist := Capsule.segDist C₁ C₂
  dist ≤ C₁.r + C₂.r

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
