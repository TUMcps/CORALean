module

public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorSpec
public import CORALean.Specification.STLInterval.Theorems.LowerStlInterval
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic

@[expose] public section

/-!
# The empty tentative signal is inconclusive everywhere

`emptySignal` is valid and, at every `t ≥ 0`, neither value can hold: the value is `Inconclusive`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem TentativeKleeneSignal.emptySignal_spec :
    TentativeKleeneSignal.emptySignal.IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      TentativeKleeneSignal.emptySignal.at t = FourValued.ii := by -- --- PROOF ---
  have hI : ∀ f, (STLInterval.stlInterval 0 ⊤ true true).fieldsOf = some f → 0 ≤ f.lower :=
    fun f hf => (STLInterval.lower_stlInterval _ _ _ _ f hf).symm.le
  obtain ⟨hv, h⟩ := PointSegmentSignal.indicator_spec _ hI false false
  refine ⟨⟨hv, hv⟩, fun t ht => ?_⟩
  simp only [TentativeKleeneSignal.emptySignal, TentativeKleeneSignal.at]
  by_cases hm : t ∈ (STLInterval.stlInterval 0 ⊤ true true).set
  · rw [(h t ht).1 hm]
  · rw [(h t ht).2 hm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
