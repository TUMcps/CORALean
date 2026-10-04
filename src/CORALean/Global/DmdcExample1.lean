import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Example 1 of the dynamic mode decomposition with control

The unstable system `x_{k+1} = [1.5 0; 0 0.1] x_k + [1; 0] u_k` under `u_k = -x_{1,k}` from
`x_1 = [4, 7]ᵀ` [1, Example 1]: the printed data matrices satisfy `X' = A X + B Υ`, and
`X` has full row rank, so `A` is the only solution of `X' - B Υ = A' X` [1, Eq. 44].
Without the input, the only solution of `X' = A' X` is the closed loop `[0.5 0; 0 0.1]`, which
is stable: DMD on the data returns the wrong dynamics (`A' ≠ A`), as the paper says it would
[1, Sec. III-B]. The rounded singular values and vectors the paper prints are not restated.

## References

* [1] J. L. Proctor, S. L. Brunton and J. N. Kutz. "Dynamic mode decomposition with control".
      SIAM Journal on Applied Dynamical Systems, 15(1):142-161, 2016 (arXiv:1409.6358).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X`, as printed. -/
noncomputable def dmdcEx1X : Mat ℝ 2 4 := !![4, 2, 1, 0.5; 7, 0.7, 0.07, 0.007]

/-- `X'`, as printed. -/
noncomputable def dmdcEx1X' : Mat ℝ 2 4 := !![2, 1, 0.5, 0.25; 0.7, 0.07, 0.007, 0.0007]

/-- `Υ`, as printed. -/
noncomputable def dmdcEx1U : Mat ℝ 1 4 := !![-4, -2, -1, -0.5]

/-- `A`, as printed. -/
noncomputable def dmdcEx1A : Mat ℝ 2 2 := !![1.5, 0; 0, 0.1]

/-- `B`, as printed. -/
noncomputable def dmdcEx1B : Mat ℝ 2 1 := !![1; 0]

/-- The printed snapshots obey `X' = A X + B Υ`. -/
theorem dmdcEx1_data : dmdcEx1X' = dmdcEx1A * dmdcEx1X + dmdcEx1B * dmdcEx1U := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dmdcEx1X', dmdcEx1A, dmdcEx1X, dmdcEx1B, dmdcEx1U] <;>
    norm_num

/-- `X` has full row rank, so a matrix is determined by its product with `X`. -/
theorem dmdcEx1_unique (A₁ A₂ : Mat ℝ 2 2) (h : A₁ * dmdcEx1X = A₂ * dmdcEx1X) :
    A₁ = A₂ := by -- --- PROOF ---
  have hM : dmdcEx1X * dmdcEx1Xᵀ = !![21.25, 29.4735; 29.4735, 49.494949] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dmdcEx1X, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> norm_num
  have hdet : (dmdcEx1X * dmdcEx1Xᵀ).det ≠ 0 := by
    rw [hM, Matrix.det_fin_two]
    simp
    norm_num
  have hu : IsUnit (dmdcEx1X * dmdcEx1Xᵀ).det := isUnit_iff_ne_zero.mpr hdet
  have h2 : A₁ * (dmdcEx1X * dmdcEx1Xᵀ) = A₂ * (dmdcEx1X * dmdcEx1Xᵀ) := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
  have := congrArg (· * (dmdcEx1X * dmdcEx1Xᵀ)⁻¹) h2
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] using this

/-- [1, Eq. 44]: with the input known, the only fit of `X' - B Υ = A' X` is `A`. -/
theorem dmdcEx1_recovers (A' : Mat ℝ 2 2) (h : dmdcEx1X' - dmdcEx1B * dmdcEx1U = A' * dmdcEx1X) :
    A' = dmdcEx1A := by
  have h2 : dmdcEx1X' - dmdcEx1B * dmdcEx1U = dmdcEx1A * dmdcEx1X := by
    exact sub_eq_iff_eq_add.mpr dmdcEx1_data
  exact dmdcEx1_unique _ _ (h.symm.trans h2)

/-- Without the input, the only fit of `X' = A' X` is the closed loop, not `A`. -/
theorem dmdcEx1_dmd_wrong (A' : Mat ℝ 2 2) (h : dmdcEx1X' = A' * dmdcEx1X) :
    A' = !![0.5, 0; 0, 0.1] ∧ A' ≠ dmdcEx1A := by -- --- PROOF ---
  have hcl : dmdcEx1X' = (!![0.5, 0; 0, 0.1] : Mat ℝ 2 2) * dmdcEx1X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dmdcEx1X', dmdcEx1X, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hA := dmdcEx1_unique _ _ (h.symm.trans hcl)
  refine ⟨hA, fun hne => ?_⟩
  have := congrFun (congrFun (hA.symm.trans hne) 0) 0
  simp [dmdcEx1A] at this
  norm_num at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
