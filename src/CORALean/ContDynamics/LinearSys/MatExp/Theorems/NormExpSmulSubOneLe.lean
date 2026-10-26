module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubOneLeExpNorm
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

@[expose] public section

/-!
# `e^{tA}` stays within `t‖A‖e^{t‖A‖}` of the identity

An unconditional bound, unlike `norm_exp_sub_expTaylor_le`'s geometric-series
estimate: comparing `exp (t • A) - 1`'s own series termwise against
`Real.exp ‖t • A‖ - 1` costs nothing extra, and `e^x - 1 ≤ x e^x` for `x ≥ 0`
closes it without any `‖t • A‖ < c` side condition. This is the bound
[1, Lemma 2]'s Appendix B needs a Lipschitz constant for `e^{AΔt}` from, over
the whole of `Δt ∈ [0, t_end]` and not only a neighbourhood of `0`.

## Inputs
* `A` – system matrix
* `t` – time

## Hypotheses
* `ht` – time nonnegative

## Conclusion
* the propagator stays within the stated distance of the identity

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e^x - 1 ≤ x e^x` for every real `x`, read off `1 - x ≤ e^{-x}` multiplied by `e^x`. -/
private theorem aux_real_exp_sub_one_le_mul_exp (x : ℝ) : -- --- CONCL ---
    Real.exp x - 1 ≤ x * Real.exp x := by -- --- PROOF ---
  have h1 : 1 + (-x) ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg x)
    linarith
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_sub, mul_one] at h2
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^{tA}` stays within `t‖A‖e^{t‖A‖}` of the identity, for every `t ≥ 0` and
with no bound on `t‖A‖` at all. -/
theorem norm_exp_smul_sub_one_le (A : Mat ℝ n n) {t : ℝ} (ht : 0 ≤ t) : -- --- CONCL ---
    ‖exp (t • A) - 1‖ ≤ t * ‖A‖ * Real.exp (t * ‖A‖) := by -- --- PROOF ---
  have h1 : ‖exp (t • A) - 1‖ ≤ Real.exp ‖t • A‖ - 1 := norm_exp_sub_one_le_exp_norm (t • A)
  have h2 : ‖t • A‖ = t * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [h2] at h1
  have h3 := aux_real_exp_sub_one_le_mul_exp (t * ‖A‖)
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
