import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowUpFloat

/-!
# `MatExp.powUp` bounds a nonnegative power from above

Induction on `k`: `mul_le_mulUp` at each step, carrying the nonnegativity
hypothesis along so the induction step may multiply an inequality by `toReal a`
without flipping it.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.le_powUp {a : 𝕋} (ha : 0 ≤ toReal a) (k : ℕ) :
    toReal a ^ k ≤ toReal (MatExp.powUp k a) := by -- --- PROOF ---
  induction k with
  | zero =>
    rw [pow_zero, MatExp.powUp, toReal_one]
  | succ k ih =>
    rw [pow_succ', MatExp.powUp]
    exact le_trans (mul_le_mul_of_nonneg_left ih ha) (mul_le_mulUp a (MatExp.powUp k a))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
