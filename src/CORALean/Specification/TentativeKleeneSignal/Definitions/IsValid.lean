module

public import CORALean.Specification.TentativeKleeneSignal.TentativeKleeneSignal
public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid

@[expose] public section

/-!
# Validity of a TentativeKleeneSignal

Both parts of a `TentativeKleeneSignal` are valid `pointSegmentSignal`s (as CORA's
constructor makes them).

## Inputs
* `T` – time type
* `s` – tentative signal

## Output
* both parts are valid signals
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both parts are valid signals. -/
def TentativeKleeneSignal.IsValid {T : Type} [LinearOrder T] [Zero T]
    (s : TentativeKleeneSignal T) : Prop :=
  s.canBeTrue.IsValid ∧ s.canBeFalse.IsValid

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
