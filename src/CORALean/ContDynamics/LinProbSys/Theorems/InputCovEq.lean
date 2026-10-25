module

public import CORALean.ContDynamics.LinProbSys.Operations.InputCov
public import CORALean.ContDynamics.LinearSys.Theorems.NoiseCovarianceDiagonal
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

/-!
# The corrected input covariance is the noise covariance of one step

For a diagonalizable `A = V diag(λ) V⁻¹`, `V` invertible and `λ` real, `inputCov V λ C r` is
`Σ_s(r) = ∫₀ʳ e^{A(r-τ)} C Cᵀ e^{Aᵀ(r-τ)} dτ` exactly, entry by entry: the exponential
conjugates to `V e^{Λs} V⁻¹`, so the integrand is `V e^{Λs} D e^{Λs} Vᵀ` with
`D = (V⁻¹C)(V⁻¹C)ᵀ`, whose `(i, j)` entry `D_ij e^{(λ_i+λ_j)s}` integrates to the closed form
`inputCov` takes, `D_ij r` where `λ_i + λ_j = 0`. CORA's own form, with the opposite sign in the
exponent, is not this covariance (`initReachCov_lt_noiseCovariance`). The noise covariance is
the one [1, Sec. II] recalls for `ẋ = Ax + u + Cξ`.

## Inputs
* `A` – system matrix
* `V` – eigenvector matrix
* `lambda` – eigenvalues
* `C` – noise matrix
* `r` – step size

## Hypotheses
* `hV` – eigenvector matrix invertible
* `hA` – `V` and `lambda` diagonalize `A`

## Conclusion
* the corrected input covariance is the one-step noise covariance

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exponential of a scaled diagonal matrix is diagonal. -/
theorem LinProbSys.aux_exp_smul_diagonal (l : Fin n → ℝ) (s : ℝ) :
    exp (s • diagonal l) = diagonal (fun i => Real.exp (s * l i)) := by
  rw [← diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  simp [Real.exp_eq_exp_ℝ]

/-- An entry of the noise covariance of a diagonal system, the case `λ_i + λ_j = 0` included. -/
theorem LinProbSys.aux_noiseCovariance_diagonal_apply (l : Fin n → ℝ) (C : Mat ℝ n m) (t : ℝ)
    (i j : Fin n) : -- --- CONCL ---
    noiseCovariance (diagonal l) C t i j
      = if l i + l j = 0 then (C * C.transpose) i j * t
        else (C * C.transpose) i j / (l i + l j)
          * (Real.exp ((l i + l j) * t) - 1) := by -- --- PROOF ---
  split_ifs with h
  · -- the integrand is the constant `(CCᵀ)ᵢⱼ`
    have hint : ∀ τ : ℝ, (exp ((t - τ) • diagonal l) * (C * C.transpose)
        * exp ((t - τ) • (diagonal l).transpose)) i j = (C * C.transpose) i j := by
      intro τ
      rw [diagonal_transpose, LinProbSys.aux_exp_smul_diagonal, mul_diagonal, diagonal_mul]
      have h1 : Real.exp ((t - τ) * l i) * Real.exp ((t - τ) * l j) = 1 := by
        rw [← Real.exp_add, ← mul_add, h, mul_zero, Real.exp_zero]
      linear_combination (C * C.transpose) i j * h1
    simp only [noiseCovariance, hint, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  · exact noiseCovariance_diagonal l C t i j h

/-- The noise covariance under a change of coordinates `A = V Λ V⁻¹`. -/
theorem LinProbSys.aux_noiseCovariance_conj (V Λ : Mat ℝ n n) (hV : IsUnit V.det)
    (C : Mat ℝ n n) (t : ℝ) : -- --- CONCL ---
    noiseCovariance (V * Λ * V⁻¹) C t
      = V * noiseCovariance Λ (V⁻¹ * C) t * Vᵀ := by -- --- PROOF ---
  have hVu : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr hV
  set D := (V⁻¹ * C) * (V⁻¹ * C)ᵀ with hD
  set g : ℝ → Mat ℝ n n := fun τ => exp ((t - τ) • Λ) * D * exp ((t - τ) • Λᵀ) with hg
  -- the exponential conjugates, and so does the integrand
  have hexp : ∀ s : ℝ, exp (s • (V * Λ * V⁻¹)) = V * exp (s • Λ) * V⁻¹ := by
    intro s
    rw [show s • (V * Λ * V⁻¹) = V * (s • Λ) * V⁻¹ by rw [Matrix.mul_smul, Matrix.smul_mul]]
    exact Matrix.exp_conj V _ hVu
  have hT : ∀ (s : ℝ) (M : Mat ℝ n n), exp (s • Mᵀ) = (exp (s • M))ᵀ := by
    intro s M
    rw [← transpose_smul, Matrix.exp_transpose]
  have hintegrand : ∀ τ : ℝ, exp ((t - τ) • (V * Λ * V⁻¹)) * (C * Cᵀ)
      * exp ((t - τ) • (V * Λ * V⁻¹)ᵀ) = V * g τ * Vᵀ := by
    intro τ
    rw [hT _ (V * Λ * V⁻¹), hexp]
    simp only [hg, hD, hT _ Λ, transpose_mul, Matrix.mul_assoc]
  -- the entries of `g` are continuous, so integrable
  have hcont : ∀ k l, Continuous fun τ => g τ k l := by
    intro k l
    have h1 : Continuous fun τ : ℝ => exp ((t - τ) • Λ) :=
      exp_continuous.comp ((continuous_const.sub continuous_id).smul continuous_const)
    have h2 : Continuous fun τ : ℝ => exp ((t - τ) • Λᵀ) :=
      exp_continuous.comp ((continuous_const.sub continuous_id).smul continuous_const)
    exact ((h1.mul continuous_const).mul h2).matrix_elem k l
  -- an entry of `V g Vᵀ` is a double sum, and the integral passes through it
  funext i j
  have hentry : ∀ τ, (V * g τ * Vᵀ) i j = ∑ k, ∑ l, V i l * g τ l k * Vᵀ k j := by
    intro τ
    simp only [Matrix.mul_apply, Finset.sum_mul]
  simp only [noiseCovariance, hintegrand, hentry]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun k _ => (continuous_finsetSum _ fun l _ =>
    ((hcont l k).const_mul _).mul_const _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum fun l _ =>
    (((hcont l k).const_mul _).mul_const _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinProbSys.inputCov_eq_noiseCovariance (A V : Mat ℝ n n) (lambda : Fin n → ℝ)
    (hV : IsUnit V.det) (hA : A = V * diagonal lambda * V⁻¹) (C : Mat ℝ n n)
    (r : ℝ) : -- --- CONCL ---
    LinProbSys.inputCov V lambda C r = noiseCovariance A C r := by -- --- PROOF ---
  -- in the eigenbasis the covariance is the diagonal one, entry by entry in closed form
  rw [hA, LinProbSys.aux_noiseCovariance_conj V _ hV C r]
  simp only [LinProbSys.inputCov]
  congr 2
  funext i j
  rw [LinProbSys.aux_noiseCovariance_diagonal_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
