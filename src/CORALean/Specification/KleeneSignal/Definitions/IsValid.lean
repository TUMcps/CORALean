module

public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid

@[expose] public section

/-!
# Validity of a KleeneSignal

Both parts of a `KleeneSignal` are valid `pointSegmentSignal`s (as CORA's
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
def KleeneSignal.IsValid {T : Type} [LinearOrder T] [Zero T] (s : KleeneSignal T) : Prop :=
  s.signal.IsValid ∧ s.isUnknown.IsValid

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
