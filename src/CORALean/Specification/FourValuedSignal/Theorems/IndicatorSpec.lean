module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Theorems.IndicatorSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorSpec
public import CORALean.Specification.FourValued.Theorems.Basic

@[expose] public section

/-!
# A four-valued indicator signal is the indicator

`indicator(interval,val,default)` is a valid signal with value `val` at the times of the interval
and `default` elsewhere: both parts are indicators, and `val` is recovered from its two parts.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.indicator_spec
    (I : STLInterval) (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) (val default : FourValued) :
    (FourValuedSignal.indicator I val default).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (FourValuedSignal.indicator I val default).at t = val) ∧
      (t ∉ I.set → (FourValuedSignal.indicator I val default).at t = default) := by -- --- PROOF ---
  obtain ⟨hv1, h1⟩ := KleeneSignal.indicator_spec I hI val.toKleene default.toKleene
  obtain ⟨hv2, h2⟩ :=
    PointSegmentSignal.indicator_spec I hI val.isInconclusive default.isInconclusive
  refine ⟨⟨hv1, hv2⟩, fun t ht => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · -- inside: the value is `val`, rebuilt from its parts
    have e1 := (h1 t ht).1 hm
    have e2 := (h2 t ht).1 hm
    have : (FourValuedSignal.indicator I val default).at t =
        FourValued.ofKleeneInc val.toKleene val.isInconclusive := by
      simp only [FourValuedSignal.at, FourValuedSignal.indicator, e1, e2, FourValued.ofKleeneInc]
    rw [this, FourValued.ofKleeneInc_toKleene_isInconclusive]
  · -- outside: the value is `default`
    have e1 := (h1 t ht).2 hm
    have e2 := (h2 t ht).2 hm
    have : (FourValuedSignal.indicator I val default).at t =
        FourValued.ofKleeneInc default.toKleene default.isInconclusive := by
      simp only [FourValuedSignal.at, FourValuedSignal.indicator, e1, e2, FourValued.ofKleeneInc]
    rw [this, FourValued.ofKleeneInc_toKleene_isInconclusive]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
