module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrectionMatrixLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiffMulVecMemCorrectionMatrix

@[expose] public section

/-!
# [1, Eq. 6]'s unscaled `ΔR = (e^{Ar} - I + F) η(R(0), γ)` misses `Δx(0) = 0`

With the correction matrix `F` of [2] (`MatExp.correctionMatrix`), `F` is second order in `r‖A‖`
while `e^{Ar} - I` is first order. In `ℝ¹` with `A = 1`, `r = 1/10` and `x(0) = 1` every
`e^{Ar} - I + F` is positive, so `Δx(0) = 0` is not in `(e^{Ar} - I + F) x(0)`; the
interpolation weight `t/r` on `e^{Ar} - I` cannot be dropped.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
* [2] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.not_expDiff_mulVec_mem_unscaled_correctionMatrix :
    ¬ ∃ F ∈ (MatExp.correctionMatrix (Matrix.diagonal fun _ : Fin 1 => (1 : ℝ)) (1 / 10)
        (0 + 2)).construct,
      exp ((0 : ℝ) • (Matrix.diagonal fun _ : Fin 1 => (1 : ℝ)))
          *ᵥ (fun _ => (1 : ℝ)) - (fun _ => (1 : ℝ))
        = ((exp ((1 / 10 : ℝ) • (Matrix.diagonal fun _ : Fin 1 => (1 : ℝ))) - 1) + F)
          *ᵥ (fun _ => (1 : ℝ)) := by -- --- PROOF ---
  rintro ⟨F, hF, h⟩
  -- the correction matrix is second order in `r‖A‖`, `e^{Ar} - 1` first order
  set A : Mat ℝ 1 1 := Matrix.diagonal fun _ : Fin 1 => (1 : ℝ) with hA
  have hnA : ‖A‖ = 1 := by
    simp [hA]
  have hnrA : ‖(1 / 10 : ℝ) • A‖ = 1 / 10 := by
    rw [norm_smul, hnA]; norm_num
  have hε : ‖(1 / 10 : ℝ) • A‖ / (((0 + 2 : ℕ) : ℝ) + 2) < 1 := by
    rw [hnrA]; norm_num
  -- the entry of `F` is within the width bound of `MatExp.abs_correctionMatrix_le`
  have hmem := (Interval.mem_mat_iff.1 hF) 0 0
  have habs := (MatExp.abs_correctionMatrix_le A (r := 1 / 10) (η := 0 + 2) (by norm_num) hε 0 0).1
  rw [abs_le] at habs
  rw [hnA] at habs
  simp only [MatExp.expRemainderBound, hnrA] at habs
  have hexp : exp ((1 / 10 : ℝ) • A) 0 0 = Real.exp (1 / 10) := by
    rw [hA, ← diagonal_smul, exp_diagonal, diagonal_apply_eq, Pi.exp_def, Real.exp_eq_exp_ℝ]
    simp
  -- coordinate 0 of the equation reads `0 = e^{r} - 1 + F`
  have h0 := congrFun h 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.sub_apply, Matrix.add_apply,
    Matrix.sub_apply, mul_one, hexp] at h0
  simp [hA] at h0
  norm_num at habs h0
  linarith [habs.1, hmem.1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
