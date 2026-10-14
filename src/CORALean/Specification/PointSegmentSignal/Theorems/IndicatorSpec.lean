module

public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorBoundsSpec
public import CORALean.Specification.STLInterval.Theorems.SetIffMemBounds
public import CORALean.Specification.STLInterval.Theorems.ZeroLeLowerBound

@[expose] public section

/-!
# An indicator signal is the indicator

`indicator(interval,val,default)` of an `stlInterval` whose lower bound is `≥ 0` is a valid signal
with value `val` at the times the interval denotes and `default` elsewhere.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.indicator_spec (I : STLInterval) (hI : ∀ f, I.fieldsOf = some f → 0 ≤
    f.lower)
    (val default : Bool) :
    (PointSegmentSignal.indicator I val default).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (PointSegmentSignal.indicator I val default).at t = val) ∧
      (t ∉ I.set →
        (PointSegmentSignal.indicator I val default).at t = default) := by -- --- PROOF ---
  obtain ⟨hv, h⟩ := PointSegmentSignal.indicatorBounds_spec I.lowerBound I.upperBound
    I.lowerClosed I.upperClosed (STLInterval.zero_le_lowerBound I hI) val default
  refine ⟨hv, fun t ht => ?_⟩
  rw [STLInterval.set_iff_memBounds I hI t]
  exact h t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
