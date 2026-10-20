module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# The Beta integral at natural exponents

`∫₀¹(1 - θ)ᵖθᵏdθ = k!p!/(k + p + 1)!`, the integral [1, Eq. 4.1] meets when the series (4.1a)
of `φ_{p+1}` is integrated term by term against (4.1b), and [1, Thm. 2] when it integrates
`Thm. 1`'s bound. By induction on `p`: `(1 - θ)^{p+1}θᵏ = (1 - θ)ᵖθᵏ - (1 - θ)ᵖθ^{k+1}`.

## Inputs
* `p` – power of one minus theta
* `k` – power of theta

## Hypotheses
* none

## Conclusion
* the Beta integral equals a ratio of factorials

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 4.1]'s step: `∫₀¹(1 - θ)ᵖθᵏdθ = k!p!/(k + p + 1)!`. -/
theorem Krylov.integral_one_sub_pow_mul_pow (p k : ℕ) :
    ∫ θ in (0 : ℝ)..1, (1 - θ) ^ p * θ ^ k =
      (Nat.factorial k * Nat.factorial p : ℝ) /
        (Nat.factorial (k + p + 1) : ℝ) := by -- --- PROOF ---
  induction p generalizing k with
  | zero =>
    simp only [pow_zero, one_mul, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero,
      Nat.factorial_zero, Nat.cast_one, mul_one, add_zero, Nat.factorial_succ, Nat.cast_mul]
    push_cast
    field_simp
  | succ p ih =>
    -- `(1 - θ)^{p+1}θᵏ = (1 - θ)ᵖθᵏ - (1 - θ)ᵖθ^{k+1}`
    have hsplit : (fun θ : ℝ => (1 - θ) ^ (p + 1) * θ ^ k) =
        fun θ => (1 - θ) ^ p * θ ^ k - (1 - θ) ^ p * θ ^ (k + 1) := by
      funext θ
      ring
    have hc : ∀ j : ℕ, Continuous fun θ : ℝ => (1 - θ) ^ p * θ ^ j := fun j => by fun_prop
    rw [hsplit, intervalIntegral.integral_sub ((hc k).intervalIntegrable _ _)
      ((hc (k + 1)).intervalIntegrable _ _), ih k, ih (k + 1)]
    rw [show k + 1 + p + 1 = k + (p + 1) + 1 by ring]
    rw [show k + (p + 1) + 1 = (k + p + 1) + 1 by ring, Nat.factorial_succ (k + p + 1),
      Nat.factorial_succ k, Nat.factorial_succ p]
    push_cast
    field_simp
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
