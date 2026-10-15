module

public import CORALean.Specification.FiniteKleeneSignalBuilder.FiniteKleeneSignalBuilder
public import CORALean.Specification.FiniteSignal.Definitions.IsValid
public import CORALean.Specification.FiniteSignal.Operations.Basic

@[expose] public section

/-!
# A valid builder

Both signals are valid `finiteSignal`s of one duration, which is what
`finiteKleeneSignalBuilder(dur)` makes them and what `setPossiblyTrue` and `setPossiblyFalse` keep.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both signals are valid and last equally long. -/
def FiniteKleeneSignalBuilder.IsValid (b : FiniteKleeneSignalBuilder) : Prop :=
  b.possiblyTrueSignal.IsValid ∧ b.possiblyFalseSignal.IsValid ∧
    b.possiblyTrueSignal.duration = b.possiblyFalseSignal.duration

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
