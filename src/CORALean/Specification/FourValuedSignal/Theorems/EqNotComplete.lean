module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.FourValuedSignal.Theorems.AtNot
public import CORALean.Specification.FourValuedSignal.Theorems.Basic

@[expose] public section

/-!
# Equality of four-valued signals is structural

`obj == other` compares the parts, so it is finer than equality of values: the Kleene part under
`isInconclusive` is irrelevant to `at`, yet negation flips it, and `a` and `~a` for a signal `a`
that is `Inconclusive` throughout have the same value everywhere but are not `==`.

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

theorem FourValuedSignal.eq_not_complete : -- --- CONCL ---
    ∃ a b : FourValuedSignal ℝ, a.IsValid ∧ b.IsValid ∧ (∀ t : ℝ, 0 ≤ t → a.at t = b.at t) ∧
      a.eq b = false := by -- --- PROOF ---
  -- the signal that is `Inconclusive` throughout, and its negation
  let a : FourValuedSignal ℝ := FourValuedSignal.uniformSignal .ii
  have ha := FourValuedSignal.uniformSignal_spec .ii
  refine ⟨a, a.not, ha.1, FourValuedSignal.not_isValid _ ha.1, fun t ht => ?_, ?_⟩
  · rw [FourValuedSignal.at_not _ ha.1, ha.2 t ht]; rfl
  · have : a.signal.signal ≠ a.not.signal.signal := by
      simp [TimeOrder.isEqvTop_iff_eq, a, FourValuedSignal.uniformSignal,
        FourValuedSignal.indicator, KleeneSignal.indicator, PointSegmentSignal.indicator,
        PointSegmentSignal.indicatorBounds, STLInterval.emptyBounds, STLInterval.lowerBound,
         STLInterval.upperBound, STLInterval.lowerClosed,
        STLInterval.upperClosed, FourValuedSignal.not, KleeneSignal.not,
        PointSegmentSignal.not, FourValued.toKleene, Kleene.toBool]
    simp [FourValuedSignal.eq, KleeneSignal.eq, this]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
