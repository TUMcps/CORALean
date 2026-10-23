module

public import CORALean.Specification.STLInterval.Operations.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The maximal intervals where a property holds

A list of `STLInterval`s lists the maximal runs of a property `P` of times: their lower bounds are
`≥ 0`, a time `t ≥ 0` is in one of them exactly when `P t`, and each is closed under paths of times
satisfying `P`: from a time in it, a time `t₂ ≥ 0` reached through times that all satisfy `P` is in
it too (so two intervals never touch). It is what the `findIntervals` of the signal classes return.

## Inputs
* `L` – list of intervals
* `P` – property of times

## Output
* the intervals are the maximal runs of times with the property
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The intervals of `L` are the maximal runs of times with the property `P`. -/
def STLInterval.MaximalRuns (L : List (STLInterval 𝕋)) (P : ℝ → Prop) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ((∃ I ∈ L, t ∈ I.set) ↔ P t)) ∧
  (∀ I ∈ L, ∀ t₁ ∈ I.set, ∀ t₂ : ℝ, 0 ≤ t₂ →
    (∀ t, 0 ≤ t → min t₁ t₂ ≤ t → t ≤ max t₁ t₂ → P t) → t₂ ∈ I.set)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
