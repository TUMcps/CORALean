module

public import CORALean.Specification.FourValuedSignal.FourValuedSignal
public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid

@[expose] public section

/-!
# Validity of a FourValuedSignal

Both parts of a `FourValuedSignal` are valid `pointSegmentSignal`s (as CORA's
constructor makes them).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both parts are valid signals. -/
def FourValuedSignal.IsValid {T : Type} [LinearOrder T] [Zero T] (s : FourValuedSignal T) : Prop :=
  s.signal.IsValid ∧ s.isInconclusive.IsValid

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
