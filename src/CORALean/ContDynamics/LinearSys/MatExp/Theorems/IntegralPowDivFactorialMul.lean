import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# `∫₀ˢ σᵏ/k! · c dσ = sᵏ⁺¹/(k+1)! · c`

The one integral every Picard estimate of a linear system takes: a bound of
order `k` at every earlier time integrates to the bound of order `k + 1`. What
makes the `k`-th Peano–Baker term `(c s)^k / k!` and the `k`-th box `s^k/k!`
times a power, rather than `(c s)^k`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.integral_pow_div_factorial_mul (k : ℕ) (s c : ℝ) :
    ∫ σ in (0:ℝ)..s, σ ^ k / (Nat.factorial k : ℝ) * c
      = s ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) * c := by -- --- PROOF ---
  simp only [div_mul_eq_mul_div, intervalIntegral.integral_div,
    intervalIntegral.integral_mul_const, integral_pow]
  rw [Nat.factorial_succ]; push_cast
  have : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
