import CORALean.ContDynamics.LinearSys.MatExp.Operations.FactorialDownFloat

/-!
# `MatExp.factorialDown` sits between one and the factorial

Held at or above `one` by the exact `maximum` in its definition, and at or
below `k!` since `k! ≥ 1` always and `nsmulDown` never overshoots it.
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

theorem MatExp.factorialDown_mem (k : ℕ) :
    1 ≤ toReal (MatExp.factorialDown (𝕋 := 𝕋) k)
      ∧ toReal (MatExp.factorialDown (𝕋 := 𝕋) k) ≤ (Nat.factorial k : ℝ) := by -- --- PROOF ---
  have h1 : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h2 : toReal (nsmulDown (Nat.factorial k) (one : 𝕋)) ≤ (Nat.factorial k : ℝ) := by
    have h := nsmulDown_le (Nat.factorial k) (one : 𝕋)
    rwa [toReal_one, mul_one] at h
  rw [MatExp.factorialDown, toReal_maximum, toReal_one]
  exact ⟨le_max_left _ _, max_le h1 h2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
