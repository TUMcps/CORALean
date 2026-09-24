import CORALean.ContDynamics.LinearSys.MatExp.Operations.FactorialUpFloat

/-!
# `MatExp.factorialUp` bounds a factorial from above

`le_nsmulUp` at `one`, `toReal one = 1` collapsing the `k!` copies to `k!`
itself.
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

theorem MatExp.factorial_le_factorialUp (k : ℕ) :
    (Nat.factorial k : ℝ) ≤ toReal (MatExp.factorialUp (𝕋 := 𝕋) k) := by
  rw [MatExp.factorialUp]
  have h := le_nsmulUp (Nat.factorial k) (one : 𝕋)
  rwa [toReal_one, mul_one] at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
