module

public import CORALean.ContSet.VPolytope.Real.Operations.Center
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# `VPolytope.center` lies in the polytope

The mean of `k > 0` vertices is the convex combination with every weight `1/k`. (For no vertices
the polytope is empty, and CORA returns an empty vector.)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.center_mem (P : VPolytope α) (hk : 0 < P.k) :
    P.center ∈ P.construct := by -- --- PROOF ---
  -- every weight is `1/k`, non-negative and summing to one
  have hk' : (0 : ℝ) < P.k := by exact_mod_cast hk
  refine ⟨fun _ => 1 / (P.k : ℝ), fun _ => div_nonneg zero_le_one hk'.le, ?_, ?_⟩
  · simp [Finset.sum_const, Finset.card_univ]
    exact mul_inv_cancel₀ hk'.ne'
  · simp only [VPolytope.center, Finset.smul_sum]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
