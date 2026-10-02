import CORALean.ContDynamics.LinParamSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinParamSys.Operations.SquaringsFloat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity

/-!
# A count `squaringsFloat` returns makes the scaled range admissible

`LinearSys.squaringsFloat_spec` at the system's interval matrix: `List.find?`
returns only an `s` its test accepted, and `le`'s `true` is sound, so
`nrm ≤ half (η + 2)↓ ≤ (η + 2)/2`. `2 ≤ η` is the caller's.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.squaringsFloat_spec
    {sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n} {Δt tLo tHi : 𝕋} {η s : ℕ}
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
