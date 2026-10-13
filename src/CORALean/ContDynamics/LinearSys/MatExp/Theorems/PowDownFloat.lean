module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowDownFloat

@[expose] public section

/-!
# `MatExp.powDown` bounds a nonnegative power from below

Induction on `k`, `mulDown_le_mul` at each step; `toReal a ≥ 0` is what lets
the step multiply the inductive bound by `toReal a` without flipping it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.powDown_le {a : 𝕋} (ha : 0 ≤ toReal a) (k : ℕ) :
    toReal (MatExp.powDown k a) ≤ toReal a ^ k := by -- --- PROOF ---
  induction k with
  | zero =>
    rw [pow_zero, MatExp.powDown, toReal_one]
  | succ k ih =>
    rw [pow_succ', MatExp.powDown]
    exact le_trans (mulDown_le_mul a (MatExp.powDown k a)) (mul_le_mul_of_nonneg_left ih ha)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
