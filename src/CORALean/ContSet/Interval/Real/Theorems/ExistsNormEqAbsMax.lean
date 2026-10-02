import CORALean.ContSet.Interval.Real.Operations.AbsMax
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import Mathlib.Analysis.Matrix.Normed

/-!
# A non-empty box has a member as long as its dominating matrix

Under the `l∞` operator norm: each entry at the endpoint of larger absolute
value is a member with the same entrywise absolute values as `absMax`, hence the
same row sums and the same norm. So `norm_le_absMax`'s bound is attained, and a
bound on every member's norm bounds `‖absMax‖` too.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A non-empty real box has a member as long as its dominating matrix: each
entry at the endpoint of larger absolute value. -/
theorem Interval.exists_norm_eq_absMax {X : Real.Interval (Mat ℝ n n)} {M₀ : Mat ℝ n n}
    (hM₀ : M₀ ∈ X.construct) : ∃ M ∈ X.construct, ‖M‖ = ‖X.absMax‖ := by -- --- PROOF ---
  classical
  have hw : ∀ i j, X.inf i j ≤ X.sup i j := fun i j =>
    (Interval.mem_mat_iff.mp hM₀ i j).1.trans (Interval.mem_mat_iff.mp hM₀ i j).2
  set M : Mat ℝ n n := Matrix.of fun i j =>
    if |X.inf i j| ≤ |X.sup i j| then X.sup i j else X.inf i j
  refine ⟨M, Interval.mem_mat_iff.mpr fun i j => ?_, ?_⟩
  · simp only [M, Matrix.of_apply]
    split_ifs <;> exact ⟨by linarith [hw i j], by linarith [hw i j]⟩
  -- entrywise the same absolute values, so the same row sums
  have habs : ∀ i j, ‖M i j‖₊ = ‖X.absMax i j‖₊ := fun i j => by
    rw [← NNReal.coe_inj, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [M, Matrix.of_apply, Interval.absMax]
    have hnn : 0 ≤ max |X.inf i j| |X.sup i j| := le_max_of_le_left (abs_nonneg _)
    rw [abs_of_nonneg hnn]
    split_ifs with h
    · exact (max_eq_right h).symm
    · exact (max_eq_left (le_of_lt (not_le.mp h))).symm
  have h : ‖M‖₊ = ‖X.absMax‖₊ := by
    rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
    simp only [habs]
  rw [← coe_nnnorm, ← coe_nnnorm X.absMax, h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
