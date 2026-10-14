module

public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.PointSegmentSignal.Theorems.SetBoundsSpec
public import CORALean.Specification.STLInterval.Theorems.SetIffMemBounds
public import CORALean.Specification.STLInterval.Theorems.ZeroLeLowerBound

@[expose] public section

/-!
# Setting a time interval sets exactly that interval

`set(obj,interval,value)` of a valid signal and an `stlInterval` whose lower bound is `≥ 0` is valid
and has `value` at the times the interval denotes, the signal's own value elsewhere: the interval's
real bounds are those of `setBounds_spec`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.set_spec (s : PointSegmentSignal ℝ) (hs : s.IsValid)
    (I : STLInterval) (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) (value : Bool) :
    (s.set I value).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (s.set I value).at t = value) ∧
      (t ∉ I.set → (s.set I value).at t = s.at t) := by -- --- PROOF ---
  obtain ⟨hv, h⟩ := PointSegmentSignal.setBounds_spec s hs I.lowerBound I.upperBound
    I.lowerClosed I.upperClosed (STLInterval.zero_le_lowerBound I hI) value
  refine ⟨hv, fun t ht => ?_⟩
  rw [STLInterval.set_iff_memBounds I hI t]
  exact h t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
