import CORALean.HybridDynamics.Definitions.RobustProjectionCora
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# `Location.robustProjectionCora` pins the box off the hyperplane

For the guard `2 x₁ = 4` (normal `(2, 0)`, `γ = 4`, hyperplane `x₁ = 2`) and the standard basis,
`aux_robustProjection` pins the first coordinate to `γ · 2 = 8`: whatever the bounds it is given,
the box it returns contains no point of the hyperplane.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The box of `aux_robustProjection` at `D = 1`, `n = (2, 0)`, `γ = 4` misses the hyperplane. -/
theorem Location.robustProjectionCora_counterexample (lb ub : Vec ℝ 2) :
    ∀ x : Vec ℝ 2, x ⬝ᵥ ![2, 0] = 4 →
      ¬ ∀ k, (Location.robustProjectionCora (1 : Mat ℝ 2 2) ![2, 0] 4 lb ub).1 k ≤ x k ∧
        x k ≤
          (Location.robustProjectionCora (1 : Mat ℝ 2 2) ![2, 0] 4 lb ub).2 k := by -- --- PROOF ---
  intro x hx hbox
  have h0 : x 0 = 2 := by
    simp [dotProduct, Fin.sum_univ_two] at hx
    linarith
  have hn : ((1 : Mat ℝ 2 2)ᵀ *ᵥ ![2, 0]) = ![2, 0] := by simp
  have h1 : ((2 : ℝ) ^ 52)⁻¹ ≤ 2 :=
    le_trans (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) (by norm_num)
  have h2 : (0 : ℝ) < 2 ^ 52 := by
    positivity
  -- only the first column is read as parallel to the normal
  have hf : (List.finRange 2).filter
      (fun i => decide ((2 : ℝ) ^ (-52 : ℤ) ≤ |((1 : Mat ℝ 2 2)ᵀ *ᵥ ![2, 0]) i|)) = [0] := by
    rw [hn]
    simp [List.finRange_succ, List.filter]
    split <;> split <;> simp_all <;> linarith [pow_pos (show (0 : ℝ) < 2 by norm_num) 52]
  have := hbox 0
  simp only [Location.robustProjectionCora, hf] at this
  simp [h0] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
