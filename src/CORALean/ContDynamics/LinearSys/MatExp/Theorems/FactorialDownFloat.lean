import CORALean.ContDynamics.LinearSys.MatExp.Operations.FactorialDownFloat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity

/-!
# `MatExp.factorialDown` sits between one and the factorial

Held at or above `one` by the exact `maximum` in its definition, and at or
below `k!` by induction: each factor, clamped at `zero`, lies in `[0, k]`, so a
product of it with the previous lower bound stays under `k · (k-1)!`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   25-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.factorialDown_mem (k : ℕ) :
    1 ≤ toReal (MatExp.factorialDown (𝕋 := 𝕋) k)
      ∧ toReal (MatExp.factorialDown (𝕋 := 𝕋) k) ≤ (Nat.factorial k : ℝ) := by -- --- PROOF ---
  induction k with
  | zero => rw [MatExp.factorialDown, toReal_one, Nat.factorial_zero, Nat.cast_one]; simp
  | succ k ih =>
    have h1 : (1 : ℝ) ≤ (Nat.factorial (k + 1) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))
    -- the factor, clamped at `zero`, lies in `[0, k + 1]`
    have hc := nsmulDown_le (k + 1) (one : 𝕋)
    rw [toReal_one, mul_one] at hc
    set c := maximum zero (nsmulDown (k + 1) (one : 𝕋))
    have hc0 : 0 ≤ toReal c := by rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
    have hck : toReal c ≤ ((k + 1 : ℕ) : ℝ) := by
      rw [toReal_maximum, toReal_zero]; exact max_le (Nat.cast_nonneg _) hc
    have hprod : toReal c * toReal (MatExp.factorialDown (𝕋 := 𝕋) k)
        ≤ (Nat.factorial (k + 1) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      exact mul_le_mul hck ih.2 (le_trans zero_le_one ih.1) (by positivity)
    rw [MatExp.factorialDown, toReal_maximum, toReal_one]
    exact ⟨le_max_left _ _, max_le h1 (le_trans (mulDown_le_mul _ _) hprod)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
