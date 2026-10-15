module

public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
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


-- ===========================  `TentativeKleeneSignal.emptySignal`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `emptySignal`: nothing observed, `canBeTrue` and `canBeFalse` false on `[0,∞)`. -/
noncomputable def TentativeKleeneSignal.emptySignal : TentativeKleeneSignal ℝ :=
  ⟨PointSegmentSignal.indicator (STLInterval.stlInterval 0 ⊤ true true) false false,
    PointSegmentSignal.indicator (STLInterval.stlInterval 0 ⊤ true true) false false⟩


-- ============================  `TentativeKleeneSignal.setInvalid`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sig = setInvalid(obj,interval)`: neither value can hold on the interval. -/
noncomputable def TentativeKleeneSignal.setInvalid (s : TentativeKleeneSignal ℝ)
    (I : STLInterval) : TentativeKleeneSignal ℝ :=
  ⟨s.canBeTrue.set I false, s.canBeFalse.set I false⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
