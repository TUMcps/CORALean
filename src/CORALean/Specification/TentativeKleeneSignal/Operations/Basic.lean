module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.TentativeKleeneSignal.TentativeKleeneSignal

@[expose] public section

/-!
# `TentativeKleeneSignal/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] [TimeOrder 𝕋]


-- ===========================  `TentativeKleeneSignal.emptySignal`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `emptySignal`: nothing observed, `canBeTrue` and `canBeFalse` false on `[0,∞)`. -/
def TentativeKleeneSignal.emptySignal [Float.ExactLe 𝕋] : TentativeKleeneSignal 𝕋 :=
  let I := STLInterval.stlInterval 0 ⊤ true true Float.toReal_zero_eq.ge
  ⟨PointSegmentSignal.indicator I false false, PointSegmentSignal.indicator I false false⟩


-- =============================  `TentativeKleeneSignal.mapTime`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The signal with every time point of both parts mapped by `f`, as a float signal is read by
`toReal`. -/
def TentativeKleeneSignal.mapTime {T T' : Type} (f : T → T') (s : TentativeKleeneSignal T) :
    TentativeKleeneSignal T' :=
  ⟨s.canBeTrue.mapTime f, s.canBeFalse.mapTime f⟩


-- ============================  `TentativeKleeneSignal.setInvalid`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sig = setInvalid(obj,interval)`: neither value can hold on the interval. -/
def TentativeKleeneSignal.setInvalid (s : TentativeKleeneSignal 𝕋) (I : STLInterval 𝕋) :
    TentativeKleeneSignal 𝕋 :=
  ⟨s.canBeTrue.set I false, s.canBeFalse.set I false⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
