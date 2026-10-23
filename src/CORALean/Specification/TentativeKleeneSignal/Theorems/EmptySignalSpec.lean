module

public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorSpec
public import CORALean.Specification.TentativeKleeneSignal.Definitions.IsValid
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic
public import CORALean.Specification.TentativeKleeneSignal.Operations.At

@[expose] public section

/-!
# The empty tentative signal is inconclusive everywhere

`emptySignal` is valid and, at every `t ≥ 0`, neither value can hold: the value is `Inconclusive`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the empty signal is valid and inconclusive everywhere
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem TentativeKleeneSignal.emptySignal_spec : -- --- CONCL ---
    (TentativeKleeneSignal.emptySignal (𝕋 := ℝ)).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (TentativeKleeneSignal.emptySignal (𝕋 := ℝ)).at t = FourValued.ii := by -- --- PROOF ---
  obtain ⟨hv, h⟩ := PointSegmentSignal.indicator_spec
    (STLInterval.stlInterval (0 : ℝ) ⊤ true true (by simp)) false false
  refine ⟨⟨hv, hv⟩, fun t ht => ?_⟩
  simp only [TentativeKleeneSignal.emptySignal, TentativeKleeneSignal.at]
  by_cases hm : t ∈ (STLInterval.stlInterval (0 : ℝ) ⊤ true true (by simp)).set
  · rw [(h t ht).1 hm]
  · rw [(h t ht).2 hm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
