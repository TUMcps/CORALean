import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# A nonempty vertex polytope has a vertex

The convex combinations of no vertices are empty (the weights must sum to `1`), so a nonempty
`VPolytope` has `k ≠ 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.k_ne_zero_of_nonempty {P : VPolytope (Vec ℝ n)} (h : P.construct.Nonempty) :
    P.k ≠ 0 := by
  intro hk
  obtain ⟨x, β, -, hsum, -⟩ := h
  haveI : IsEmpty (Fin P.k) := by rw [hk]; infer_instance
  simp at hsum


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
