module

public import CORALean.ContDynamics.LinearSys.Definitions.IsOrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.Operations.HalvingsFloat
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# A count `halvingsFloat` returns makes the scaled step admissible

`List.find?` returns only an `s` its test accepted, and `le`'s `true` is sound: the float norm
bound of the scaled matrix is at most `half one = 1/2`, so its quotient by `η + 2 ≥ 4` is at
most `1/2` at every order `η ≥ 2`.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order

## Hypotheses
* `h2` – order at least two

## Conclusion
* every returned count makes the scaled step admissible
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.halvingsFloat_spec {sys : LinearSys 𝕋 n} {Δt : 𝕋} {η : ℕ}
    (h2 : 2 ≤ η) : -- --- CONCL ---
    ∀ s ∈ sys.halvingsFloat Δt,
      sys.IsOrderAdmissibleFloat (half^[s] Δt) (half^[s] Δt) η := by -- --- PROOF ---
  intro s (h : sys.halvingsFloat Δt = some s)
  have htest := List.find?_some h
  refine ⟨h2, ?_⟩
  have hle := toReal_le_of_le htest
  rw [toReal_half, toReal_one] at hle
  have hη : (4 : ℝ) ≤ (η : ℝ) + 2 := by
    have : (2 : ℝ) ≤ η := by exact_mod_cast h2
    linarith
  rw [div_le_iff₀ (by linarith)]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
