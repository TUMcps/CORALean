module

public import CORALean.Specification.Kleene.Kleene
public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.TentativeKleeneSignal.TentativeKleeneSignal

@[expose] public section

/-!
# Observing a value on an interval

`sig = observe(obj,interval,value)` of `tentativeKleeneSignal.m`: `True` lets `canBeTrue` hold on
the interval, `False` lets `canBeFalse` hold, `Unknown` both; the other part is left alone. CORA's
`otherwise` branch (`assert(false)`) is a value that is no Kleene value, which `Kleene` has none
of.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = observe(obj,interval,value)`. -/
noncomputable def TentativeKleeneSignal.observe (s : TentativeKleeneSignal ℝ) (I : STLInterval)
    (value : Kleene) : TentativeKleeneSignal ℝ :=
  match value with
  -- `case kleene.True`
  | .tt => ⟨s.canBeTrue.set I true, s.canBeFalse⟩
  -- `case kleene.False`
  | .ff => ⟨s.canBeTrue, s.canBeFalse.set I true⟩
  -- `case kleene.Unknown`
  | .uu => ⟨s.canBeTrue.set I true, s.canBeFalse.set I true⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
