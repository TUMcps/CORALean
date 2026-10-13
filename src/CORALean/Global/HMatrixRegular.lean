import CORALean.Global.HMatrix
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# H-matrices are regular

[1, Remark 4.1]: a strictly diagonally dominant interval matrix is an H-matrix, at `u = 1`;
[1, Thm. 4.9] (cited from Neumaier's book): every real matrix in an H-matrix is regular,
since `A diag(u)` is strictly diagonally dominant and Lévy–Desplanques
(`det_ne_zero_of_sum_row_lt_diag`, [1, Thm. 4.6]) applies. The interval matrix enters
through bounds on `|A|`: its mignitudes below on the diagonal, magnitudes above off it.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Finset

variable {k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Remark 4.1]: a strictly diagonally dominant interval matrix is an H-matrix. -/
theorem isHMatrix_of_dominant {mig mag : Matrix (Fin k) (Fin k) ℝ}
    (h : ∀ i, ∑ j ∈ univ.erase i, mag i j < mig i i) : IsHMatrix mig mag :=
  ⟨fun _ => 1, fun _ => one_pos, fun i => by
    rw [compMat_mulVec_apply]; simpa only [mul_one, sub_pos] using h i⟩

/-- [1, Thm. 4.9]: every real matrix in an H-matrix is regular. -/
theorem det_ne_zero_of_isHMatrix {mig mag : Matrix (Fin k) (Fin k) ℝ} (hH : IsHMatrix mig mag)
    (A : Matrix (Fin k) (Fin k) ℝ) (hmig : ∀ i, mig i i ≤ |A i i|)
    (hmag : ∀ i j, i ≠ j → |A i j| ≤ mag i j) : A.det ≠ 0 := by -- --- PROOF ---
  obtain ⟨u, hu, hAu⟩ := hH
  -- `A diag(u)` is strictly row-dominant
  have hdom : ∀ i, ∑ j ∈ univ.erase i, ‖(A * diagonal u) i j‖ < ‖(A * diagonal u) i i‖ := by
    intro i
    have h := hAu i
    rw [compMat_mulVec_apply, sub_pos] at h
    simp only [mul_diagonal, Real.norm_eq_abs, abs_mul, abs_of_pos (hu _)]
    calc ∑ j ∈ univ.erase i, |A i j| * u j ≤ ∑ j ∈ univ.erase i, mag i j * u j :=
          sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_right (hmag i j (ne_of_mem_erase hj).symm) (hu j).le
      _ < mig i i * u i := h
      _ ≤ |A i i| * u i := mul_le_mul_of_nonneg_right (hmig i) (hu i).le
  have hne := det_ne_zero_of_sum_row_lt_diag hdom
  rw [det_mul] at hne
  exact left_ne_zero_of_mul hne

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
