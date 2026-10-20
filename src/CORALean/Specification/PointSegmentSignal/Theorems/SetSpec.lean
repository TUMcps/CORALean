module

public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.PointSegmentSignal.Theorems.SetBoundsSpec
public import CORALean.Specification.STLInterval.Theorems.SetIffMemBounds
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# Setting a time interval sets exactly that interval

`set(obj,interval,value)` of a valid signal and an `stlInterval` whose lower bound is `≥ 0` is valid
and has `value` at the times the interval denotes, the signal's own value elsewhere: the interval's
real bounds are those of `setBounds_spec`.

## Inputs
* `s` – signal
* `I` – time interval
* `value` – value to set

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* a valid signal with the value on the interval and unchanged elsewhere
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.set_spec (s : PointSegmentSignal ℝ) (hs : s.IsValid)
    (I : STLInterval) (value : Bool) : -- --- CONCL ---
    (s.set I value).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (s.set I value).at t = value) ∧
      (t ∉ I.set → (s.set I value).at t = s.at t) := by -- --- PROOF ---
  obtain ⟨hv, h⟩ := PointSegmentSignal.setBounds_spec s hs I.lowerBound I.upperBound
    I.lowerClosed I.upperClosed (STLInterval.zero_le_lowerBound I) value
  refine ⟨hv, fun t ht => ?_⟩
  rw [STLInterval.set_iff_memBounds I t]
  exact h t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
