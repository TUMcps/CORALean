module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.IsValid
public import CORALean.Specification.FiniteSignal.Operations.At

@[expose] public section

/-!
# What a builder says

A builder says, for a duration `d`, that the property can be true at the times `t` of `[0,d]` with
`PT t` and can be false at those with `PF t`: it is valid, lasts `d`, and its two signals are true
at `t` exactly there.

## Inputs
* `b` – signal builder
* `d` – duration
* `PT` – times where the property can be true
* `PF` – times where the property can be false

## Output
* the builder is valid, lasts `d` and marks `PT` and `PF`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The builder marks `PT` as possibly true and `PF` as possibly false on `[0,d]`. -/
def FiniteKleeneSignalBuilder.Represents (b : FiniteKleeneSignalBuilder ℝ) (d : ℝ)
    (PT PF : ℝ → Prop) : Prop :=
  b.IsValid ∧ b.possiblyTrueSignal.duration = d ∧ ∀ t : ℝ, 0 ≤ t → t ≤ d →
    (∃ x, b.possiblyTrueSignal.at? t = some x ∧ (x = true ↔ PT t)) ∧
    (∃ y, b.possiblyFalseSignal.at? t = some y ∧ (y = true ↔ PF t))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
