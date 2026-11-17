module

public import Mathlib.Analysis.Matrix.Normed
public import CORALean.Global.Tensor

@[expose] public section

/-!
# Bounding the `l∞` norm by the rows

The `l∞` operator norm is the largest absolute row sum (`Matrix.linfty_opNorm_def`), so a bound
`b ≥ 0` on every row's absolute sum bounds the norm.

## Inputs
* `M` – matrix
* `b` – row bound

## Hypotheses
* `hb` – the bound is nonnegative
* `h` – every row's absolute sum is at most `b`

## Conclusion
* `‖M‖ ≤ b`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.norm_le_of_sum_abs_le (M : Mat ℝ n n) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ j, ∑ k, |M j k| ≤ b) : -- --- CONCL ---
    ‖M‖ ≤ b := by -- --- PROOF ---
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i => ∑ j, ‖M i j‖₊) ≤ (⟨b, hb⟩ : NNReal) := by
    refine Finset.sup_le fun i _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum]
    have := h i
    simp only [coe_nnnorm, Real.norm_eq_abs]
    exact this
  exact_mod_cast this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
