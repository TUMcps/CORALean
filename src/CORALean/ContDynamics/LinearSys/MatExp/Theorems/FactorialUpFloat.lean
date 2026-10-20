module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.FactorialUpFloat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `MatExp.factorialUp` bounds a factorial from above

By induction: `le_nsmulUp` at `one` puts each factor at or above `k`, and a
product of nonnegative upper bounds is one, so `mulUp` stays above `k · (k-1)!`.

## Inputs
* `k` – factorial argument

## Hypotheses
* none

## Conclusion
* the factorial is at most its float upper bound
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   25-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.factorial_le_factorialUp (k : ℕ) :
    (Nat.factorial k : ℝ) ≤ toReal (MatExp.factorialUp (𝕋 := 𝕋) k) := by -- --- PROOF ---
  induction k with
  | zero => rw [MatExp.factorialUp, toReal_one, Nat.factorial_zero, Nat.cast_one]
  | succ k ih =>
    -- the factor never undershoots `k + 1`, and both factors are nonnegative
    have hc := le_nsmulUp (k + 1) (one : 𝕋)
    rw [toReal_one, mul_one] at hc
    rw [MatExp.factorialUp, Nat.factorial_succ, Nat.cast_mul]
    refine le_trans ?_ (mul_le_mulUp _ _)
    exact mul_le_mul hc ih (by positivity) (le_trans (by positivity) hc)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
