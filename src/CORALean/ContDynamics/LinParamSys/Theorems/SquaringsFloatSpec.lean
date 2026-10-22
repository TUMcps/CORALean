module

public import CORALean.ContDynamics.LinParamSys.Definitions.OrderAdmissibleFloat
public import CORALean.ContDynamics.LinParamSys.Operations.SquaringsFloat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.Interval.Float.Instances

@[expose] public section

/-!
# A count `squaringsFloat` returns makes the scaled range admissible

`LinearSys.squaringsFloat_spec` at the system's interval matrix: `List.find?`
returns only an `s` its test accepted, and `le`'s `true` is sound, so
`nrm ≤ half (η + 2)↓ ≤ (η + 2)/2`. `2 ≤ η` is the caller's.

## Inputs
* `sys` – system
* `Δt` – window length
* `tLo` – lower time bound
* `tHi` – upper time bound
* `η` – Taylor order

## Hypotheses
* `h2` – order at least two

## Conclusion
* a returned count makes the scaled time range admissible
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.squaringsFloat_spec {sys : LinParamSys ℐ[𝕋] n}
    {Δt tLo tHi : 𝕋} {η : ℕ} (h2 : 2 ≤ η) : -- --- CONCL ---
    ∀ s ∈ sys.squaringsFloat Δt tLo tHi η,
      sys.OrderAdmissibleFloat (half^[s] tLo) (half^[s] tHi) η := by -- --- PROOF ---
  intro s (h : sys.squaringsFloat Δt tLo tHi η = some s)
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
