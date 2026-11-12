module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.QuadExpLeWeighted

@[expose] public section

/-!
# The 2-norm of `e^{tA}x` grows at most by `√(b/a) e^{μt}` for a Lyapunov weight

With a symmetric weight `P` of rate `μ` (`x*PAx ≤ μ x*Px`, `Krylov.quad_exp_le_weighted`) and `a
x*x ≤ x*Px ≤ b x*x`, the 2-norm of `e^{tA}x` grows by at most `√(b/a) e^{μt}`: [1, Eq. 3.4]'s
bound with the weight's condition number in place of Gershgorin's rate. `μ` may be negative, `b/a`
is the price.

## Inputs
* `A` – matrix
* `P` – symmetric weight
* `μ` – growth rate in the weight
* `a` – lower bound of the weight's quadratic form
* `b` – upper bound of the weight's quadratic form
* `x` – start vector
* `t` – time

## Hypotheses
* `hS` – weight symmetric
* `hPA` – `x*PAx ≤ μ x*Px`
* `ha` – `a x*x ≤ x*Px`
* `hb` – `x*Px ≤ b x*x`
* `ha0` – `a` positive
* `hb0` – `b` nonnegative
* `ht` – time nonnegative

## Conclusion
* the 2-norm grows by at most `√(b/a) e^{μt}`

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `a x*x ≤ x*Px ≤ b x*x`, `a > 0`: `‖e^{tA}x‖₂ ≤ √(b/a) e^{μt} ‖x‖₂` for `t ≥ 0`. -/
theorem Krylov.norm_exp_le_weighted (A P : Mat ℝ n n) (μ a b : ℝ) (hS : Pᵀ = P)
    (hPA : ∀ x, x ⬝ᵥ (P *ᵥ (A *ᵥ x)) ≤ μ * (x ⬝ᵥ (P *ᵥ x)))
    (ha : ∀ x, a * (x ⬝ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)) (hb : ∀ x, x ⬝ᵥ (P *ᵥ x) ≤ b * (x ⬝ᵥ x))
    (ha0 : 0 < a) (hb0 : 0 ≤ b) (x : Vec ℝ n) {t : ℝ} (ht : 0 ≤ t) : -- --- CONCL ---
    ‖exp (t • A) *ᵥ x‖₂ ≤ Real.sqrt (b / a) * Real.exp (μ * t) * ‖x‖₂ := by -- --- PROOF ---
  have h := Krylov.quad_exp_le_weighted A P μ hS hPA x ht
  -- squared: `a ‖e^{tA}x‖² ≤ e^{2μt} b ‖x‖²`
  have h1 := ha (exp (t • A) *ᵥ x)
  have h2 := hb x
  rw [dotProduct_self] at h1 h2
  have h3 : a * ‖exp (t • A) *ᵥ x‖₂ ^ 2 ≤ Real.exp (2 * μ * t) * (b * ‖x‖₂ ^ 2) :=
    h1.trans (h.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le))
  have hsq : (Real.sqrt (b / a) * Real.exp (μ * t) * ‖x‖₂) ^ 2 =
      b / a * Real.exp (2 * μ * t) * ‖x‖₂ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hb0 ha0.le), ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hq : ‖exp (t • A) *ᵥ x‖₂ ^ 2 ≤ (Real.sqrt (b / a) * Real.exp (μ * t) * ‖x‖₂) ^ 2 := by
    rw [hsq, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ ha0]
    linarith
  have hnn : 0 ≤ Real.sqrt (b / a) * Real.exp (μ * t) * ‖x‖₂ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) (norm₂_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm₂_nonneg _) hnn two_ne_zero).1 hq


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
