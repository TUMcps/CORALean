module

public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.Theorems.IndicatorSpec
public import CORALean.Specification.KleeneSignal.Theorems.Basic
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# Equality of Kleene signals is structural

`obj == other` compares the Boolean and unknown parts, so it is finer than equality of values: the
Boolean part under `isUnknown` is irrelevant to `at`, yet negation flips it, and `a` and `~a` for a
signal `a` that is `Unknown` throughout have the same value everywhere but are not `==`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* two valid signals with equal values at all times compare unequal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.eq_not_complete : -- --- CONCL ---
    ∃ a b : KleeneSignal ℝ, a.IsValid ∧ b.IsValid ∧ (∀ t : ℝ, 0 ≤ t → a.at t = b.at t) ∧
      a.eq b = false := by -- --- PROOF ---
  -- the signal that is `Unknown` throughout, and its negation
  let a : KleeneSignal ℝ := KleeneSignal.indicator STLInterval.empty .uu .uu
  have ha : a.IsValid ∧ ∀ t : ℝ, 0 ≤ t → a.at t = .uu := by
    obtain ⟨hv, hat⟩ := KleeneSignal.indicator_spec STLInterval.empty .uu .uu
    exact ⟨hv, fun t ht =>
      (hat t ht).2 (by simp [STLInterval.set_empty])⟩
  refine ⟨a, a.not, ha.1, KleeneSignal.not_isValid _ ha.1, fun t ht => ?_, ?_⟩
  · rw [KleeneSignal.at_not _ ha.1, ha.2 t ht]; rfl
  · have : a.signal ≠ a.not.signal := by
      simp [TimeOrder.isEqvTop_iff_eq, a, KleeneSignal.indicator, PointSegmentSignal.indicator,
          PointSegmentSignal.indicatorBounds, STLInterval.emptyBounds,
        STLInterval.lowerBound, STLInterval.upperBound, STLInterval.lowerClosed,
        STLInterval.upperClosed, KleeneSignal.not,
        PointSegmentSignal.not, Kleene.toBool]
    simp [KleeneSignal.eq, this]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
