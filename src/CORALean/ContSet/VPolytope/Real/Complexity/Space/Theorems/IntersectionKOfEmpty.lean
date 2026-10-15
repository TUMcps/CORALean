module

public import CORALean.ContSet.VPolytope.Real.Operations.Intersection

@[expose] public section

/-!
# `VPolytope.intersection_k_of_empty`

The `k_of_empty` count of `intersection`'s result.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n q₁ q₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `k_of_empty` count of `intersection`'s result. -/
theorem VPolytope.intersection_k_of_empty (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ))
    (h : ¬(VPolytope.intersectionH P₁ P₂ Aq₁ Aq₂).construct.Nonempty) :
    (VPolytope.intersection P₁ P₂ Aq₁ Aq₂).k = 0 := by
  unfold VPolytope.intersection
  rw [dif_neg h]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
