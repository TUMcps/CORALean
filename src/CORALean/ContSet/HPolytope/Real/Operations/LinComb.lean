import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
import CORALean.ContSet.ContSet.SupportBound

/-!
# `HPolytope.linCombOf`

CORA's `linComb`, on chosen directions: a point between the two polytopes is a
weighted average of one from each, so it beats neither bound and the larger of
the two serves.

A halfspace description is convex, so here `linComb` and the convex hull agree;
the distinction the interface keeps is for representations that are not.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ} {P₁ P₂ : HPolytope α}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.linCombOf (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u₁ : ∀ i, SupportBound P₁.construct (Aq i))
    (u₂ : ∀ i, SupportBound P₂.construct (Aq i)) : HPolytope α :=
  HPolytope.ofBounds Aq fun i => (u₁ i).segments (u₂ i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
