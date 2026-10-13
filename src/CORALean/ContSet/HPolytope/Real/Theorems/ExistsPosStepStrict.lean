import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-!
# Strict inequalities survive a small step

Finitely many strict inequalities `A z < c` still hold at `z + s d` for some `s > 0`, whatever
the direction `d`: the step `s = 1 / (1 + ∑ᵢ (|(A d)ᵢ| + 1) / (cᵢ - (A z)ᵢ))` is short enough for
every row at once. Explicit, so no topology is needed where a facet argument steps off a point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.exists_pos_step_strict (A : Mat ℝ q n) (c : Vec ℝ q) (z d : Vec ℝ n)
    (hz : ∀ i, (A *ᵥ z) i < c i) :
    ∃ s : ℝ, 0 < s ∧ ∀ i, (A *ᵥ (z + s • d)) i < c i := by -- --- PROOF ---
  set T := 1 + ∑ i, (|(A *ᵥ d) i| + 1) / (c i - (A *ᵥ z) i) with hT
  have hterm : ∀ i, 0 ≤ (|(A *ᵥ d) i| + 1) / (c i - (A *ᵥ z) i) := fun i =>
    div_nonneg (by positivity) (sub_pos.mpr (hz i)).le
  have hT1 : 1 ≤ T := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hterm i)
  refine ⟨1 / T, by positivity, fun i => ?_⟩
  have hsl := sub_pos.mpr (hz i)
  have hle : (|(A *ᵥ d) i| + 1) / (c i - (A *ᵥ z) i) ≤ T :=
    le_trans (Finset.single_le_sum (f := fun i => (|(A *ᵥ d) i| + 1) / (c i - (A *ᵥ z) i))
      (fun i _ => hterm i) (Finset.mem_univ i)) (le_add_of_nonneg_left zero_le_one)
  rw [div_le_iff₀ hsl] at hle
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hTpos : 0 < T := by linarith
  -- `s (A d)ᵢ ≤ s |(A d)ᵢ| < s (|(A d)ᵢ| + 1) ≤ slack`
  have h1 : 1 / T * (A *ᵥ d) i < 1 / T * (|(A *ᵥ d) i| + 1) :=
    mul_lt_mul_of_pos_left (by linarith [le_abs_self ((A *ᵥ d) i)]) (by positivity)
  have h2 : 1 / T * (|(A *ᵥ d) i| + 1) ≤ c i - (A *ᵥ z) i := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hTpos]
    linarith
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
