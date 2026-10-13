import CORALean.ContSet.Interval.Real.Operations.AbsMax
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import Mathlib.Analysis.Matrix.Normed

/-!
# `Interval.absMax` dominates the norm of every member of the box

Under the `l∞` operator norm: entrywise, `M i j` sits between `A`'s endpoints so
`|M i j| ≤ A.absMax i j`, and `A.absMax i j` is its own absolute value since it
is non-negative; summing that domination over a row and taking the sup over
rows carries it from entries to the whole norm.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point between two endpoints never exceeds the max of their absolute
values, whichever endpoint is bigger. -/
theorem aux_abs_le_max_abs {lo hi x : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    |x| ≤ max |lo| |hi| := by
  refine abs_le.mpr ⟨?_, h2.trans ((le_abs_self hi).trans (le_max_right _ _))⟩
  linarith [(neg_abs_le lo).trans h1, neg_le_neg (le_max_left |lo| |hi|)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The dominating matrix bounds the norm of every member of the box. -/
theorem Interval.norm_le_absMax {A : Interval (Mat ℝ m n)} {M : Mat ℝ m n}
    (hM : M ∈ A.construct) : ‖M‖ ≤ ‖A.absMax‖ := by -- --- PROOF ---
  have hentry : ∀ i j, ‖M i j‖₊ ≤ ‖A.absMax i j‖₊ := by
    intro i j
    have h := Interval.mem_mat_iff.mp hM i j
    have hnonneg : (0:ℝ) ≤ A.absMax i j := le_max_of_le_left (abs_nonneg _)
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hnonneg]
    exact aux_abs_le_max_abs h.1 h.2
  have h : ‖M‖₊ ≤ ‖A.absMax‖₊ := by
    rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
    exact Finset.sup_mono_fun fun i _ => Finset.sum_le_sum fun j _ => hentry i j
  exact_mod_cast h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
