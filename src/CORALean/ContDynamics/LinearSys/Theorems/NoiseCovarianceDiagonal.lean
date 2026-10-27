module

public import CORALean.ContDynamics.LinearSys.Definitions.NoiseCovariance
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# The noise covariance of a diagonal system, in closed form

[1, Sec. II] diagonalizes `A` to `A* = diag(λ)` and states
`[Σ*_s(t)]ᵢⱼ = (C*C*ᵀ)ᵢⱼ / (λᵢ + λⱼ) · (1 - e^{(-λᵢ-λⱼ)t})`. The integrand of `Σ_s` is
`(CCᵀ)ᵢⱼ e^{(λᵢ+λⱼ)(t-τ)}`, which integrates over `[0, t]` to
`(CCᵀ)ᵢⱼ / (λᵢ + λⱼ) · (e^{(λᵢ+λⱼ)t} - 1)`: the printed form is the one for the drift `-A`,
the sign convention `dx = -Ax dt + B dW` of the handbook [1] cites, not for [1]'s own
`ẋ = Ax + …`. `NoiseCovarianceDiagonal` separates the two. Stated for real
eigenvalues with `λᵢ + λⱼ ≠ 0`, which the division needs.

## Inputs
* `l` – diagonal entries
* `C` – noise matrix
* `t` – time
* `i` – row index
* `j` – column index

## Hypotheses
* `h` – sum of the two diagonal entries nonzero

## Conclusion
* the covariance entry has the closed form

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.](../../../../../references/2009/althoff-ecc-enclosing-hulls.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `∫₀ᵗ e^{a(t-τ)} dτ = (e^{at} - 1)/a`. -/
private theorem aux_integral_exp_sub (a t : ℝ) (ha : a ≠ 0) : -- --- CONCL ---
    ∫ τ in (0 : ℝ)..t, Real.exp (a * (t - τ)) = (Real.exp (a * t) - 1) / a := by -- --- PROOF ---
  rw [intervalIntegral.integral_comp_sub_left (fun s => Real.exp (a * s)) t]
  simp only [sub_self, sub_zero]
  rw [intervalIntegral.integral_comp_mul_left (fun s => Real.exp s) ha, integral_exp]
  simp [mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp

/-- The exponential of a scaled diagonal matrix is diagonal. -/
private theorem aux_exp_smul_diagonal (l : Fin n → ℝ) (s : ℝ) :
    NormedSpace.exp (s • diagonal l) = diagonal (fun i => Real.exp (s * l i)) := by
  rw [← diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  simp [Real.exp_eq_exp_ℝ]


-- =======================================  MAIN THEOREM  ======================================= --

theorem noiseCovariance_diagonal (l : Fin n → ℝ) (C : Mat ℝ n m) (t : ℝ) (i j : Fin n)
    (h : l i + l j ≠ 0) : -- --- CONCL ---
    noiseCovariance (diagonal l) C t i j
      = (C * C.transpose) i j / (l i + l j)
        * (Real.exp ((l i + l j) * t) - 1) := by -- --- PROOF ---
  -- the integrand is `(CCᵀ)ᵢⱼ e^{(λᵢ+λⱼ)(t-τ)}`
  have hint : ∀ τ : ℝ, (NormedSpace.exp ((t - τ) • diagonal l) * (C * C.transpose)
      * NormedSpace.exp ((t - τ) • (diagonal l).transpose)) i j
      = (C * C.transpose) i j * Real.exp ((l i + l j) * (t - τ)) := by
    intro τ
    rw [diagonal_transpose, aux_exp_smul_diagonal, mul_diagonal, diagonal_mul, add_mul,
      Real.exp_add]
    ring_nf
  simp only [noiseCovariance, hint, intervalIntegral.integral_const_mul,
    aux_integral_exp_sub _ _ h]
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
