module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.Basic
public import Mathlib.Analysis.Matrix.Normed
public import CORALean.Global.Tensor

@[expose] public section

/-!
# A row vector times a matrix, in the weighted `l¹` norm

For positive scales `s`, `Σⱼ |(e M)ⱼ| sⱼ ≤ (Σᵢ |eᵢ| sᵢ) ‖S⁻¹ M S‖`: the weighted `l¹` norm of
row vectors is the dual of the balanced `l∞` norm of matrices. Each `|(e M)ⱼ|` is at most
`Σᵢ |eᵢ||Mᵢⱼ|`, and the sum over `j` regroups as `Σᵢ |eᵢ| sᵢ` times row `i` of `S⁻¹ |M| S`, at
most its norm. A direction propagated by `e^{AΔt}` therefore keeps an error measured this way
bounded by the balanced norms of the powers.

## Inputs
* `s` – scales
* `e` – row vector
* `M` – matrix

## Hypotheses
* `hs` – the scales are positive

## Conclusion
* the weighted norm of `e M` is at most that of `e` times the balanced norm of `M`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem MatExp.aux_sum_abs_le_norm (M : Mat ℝ n n) (i : Fin n) :
    ∑ j, |M i j| ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h := Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have h' : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ _ := NNReal.coe_le_coe.mpr h
  simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h'


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.weightedSum_vecMul_le {s : Fin n → ℝ} (hs : ∀ i, 0 < s i) (e : Fin n → ℝ)
    (M : Mat ℝ n n) : -- --- CONCL ---
    ∑ j, |(e ᵥ* M) j| * s j
      ≤ (∑ i, |e i| * s i) * ‖MatExp.scaleConj s M‖ := by -- --- PROOF ---
  have happ : ∀ i j, MatExp.scaleConj s M i j = M i j * s j / s i := by
    intro i j; simp [MatExp.scaleConj, Matrix.mul_diagonal, Matrix.diagonal_mul]; ring
  calc ∑ j, |(e ᵥ* M) j| * s j
      ≤ ∑ j, ∑ i, |e i| * |M i j| * s j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hv : (e ᵥ* M) j = ∑ i, e i * M i j := rfl
        rw [hv]
        refine le_trans (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
          (hs j).le) (le_of_eq ?_)
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by rw [abs_mul]
    -- regrouped by `i`: row `i` of `S⁻¹ |M| S`
    _ = ∑ i, (|e i| * s i) * ∑ j, |MatExp.scaleConj s M i j| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [happ, abs_div, abs_mul, abs_of_pos (hs i), abs_of_pos (hs j)]
        field_simp [(hs i).ne']
    _ ≤ ∑ i, (|e i| * s i) * ‖MatExp.scaleConj s M‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (MatExp.aux_sum_abs_le_norm _ i)
          (mul_nonneg (abs_nonneg _) (hs i).le)
    _ = _ := by rw [Finset.sum_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
