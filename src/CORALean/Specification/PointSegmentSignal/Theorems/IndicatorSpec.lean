module

public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorBoundsSpec
public import CORALean.Specification.STLInterval.Theorems.SetIffMemBounds
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# An indicator signal is the indicator

`indicator(interval,val,default)` of an `stlInterval` is a valid signal
with value `val` at the times the interval denotes and `default` elsewhere.

## Inputs
* `I` – time interval
* `val` – value on the interval
* `default` – value elsewhere

## Hypotheses
* none

## Conclusion
* a valid signal that is `val` on the interval and `default` elsewhere
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.indicator_spec (I : STLInterval)
    (val default : Bool) : -- --- CONCL ---
    (PointSegmentSignal.indicator I val default).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (PointSegmentSignal.indicator I val default).at t = val) ∧
      (t ∉ I.set →
        (PointSegmentSignal.indicator I val default).at t = default) := by -- --- PROOF ---
  obtain ⟨hv, h⟩ := PointSegmentSignal.indicatorBounds_spec I.lowerBound I.upperBound
    I.lowerClosed I.upperClosed (STLInterval.zero_le_lowerBound I) val default
  refine ⟨hv, fun t ht => ?_⟩
  rw [STLInterval.set_iff_memBounds I t]
  exact h t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
