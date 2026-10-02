import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinearSys.Operations.SquaringsFloat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity

/-!
# A count `squaringsFloat` returns makes the scaled range admissible

`List.find?` returns only an `s` its test accepted, and `le`'s `true` is sound:
`nrm ≤ half (η + 2)↓ ≤ (η + 2)/2`, `half` exact and the count rounded down —
`admissibleOrder_spec`'s argument at the scaled range. The other test, the
step's norm, is precision and not needed here. `2 ≤ η` is the caller's.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.squaringsFloat_spec {sys : LinearSys 𝕋 n} {Δt tLo tHi : 𝕋} {η s : ℕ}
    (h2 : 2 ≤ η) (h : sys.squaringsFloat Δt tLo tHi η = some s) :
    sys.OrderAdmissibleFloat (half^[s] tLo) (half^[s] tHi) η := by -- --- PROOF ---
  have htest := List.find?_some h
  simp only [Bool.and_eq_true] at htest
  refine ⟨h2, ?_⟩
  -- `half` is exact and the count is rounded down, so `nrm ≤ (η + 2)/2`
  have hle := toReal_le_of_le htest.2
  have hcount := nsmulDown_le (η + 2) (one : 𝕋)
  rw [toReal_one, mul_one] at hcount
  rw [toReal_half] at hle
  have hpos : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  rw [div_le_iff₀ hpos]
  push_cast at hcount
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
