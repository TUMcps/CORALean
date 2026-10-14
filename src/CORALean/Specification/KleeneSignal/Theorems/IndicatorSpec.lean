module

public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorSpec
public import CORALean.Specification.Kleene.Theorems.Basic

@[expose] public section

/-!
# A Kleene indicator signal is the indicator

`indicator(interval,val,default)` is a valid signal with value `val` at the times of the interval
and `default` elsewhere: both parts are indicators, and `val` is recovered from its two parts.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.indicator_spec (I : STLInterval)
    (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) (val default : Kleene) :
    (KleeneSignal.indicator I val default).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (KleeneSignal.indicator I val default).at t = val) ∧
      (t ∉ I.set → (KleeneSignal.indicator I val default).at t = default) := by -- --- PROOF ---
  obtain ⟨hv1, h1⟩ := PointSegmentSignal.indicator_spec I hI val.toBool default.toBool
  obtain ⟨hv2, h2⟩ := PointSegmentSignal.indicator_spec I hI val.isUnknown default.isUnknown
  refine ⟨⟨hv1, hv2⟩, fun t ht => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · -- inside: the value is `val`, rebuilt from its parts
    have e1 := (h1 t ht).1 hm
    have e2 := (h2 t ht).1 hm
    have : (KleeneSignal.indicator I val default).at t =
        Kleene.ofBoolUnk val.toBool val.isUnknown := by
      simp only [KleeneSignal.at, KleeneSignal.indicator, e1, e2, Kleene.ofBoolUnk]
    rw [this, Kleene.ofBoolUnk_toBool_isUnknown]
  · -- outside: the value is `default`
    have e1 := (h1 t ht).2 hm
    have e2 := (h2 t ht).2 hm
    have : (KleeneSignal.indicator I val default).at t =
        Kleene.ofBoolUnk default.toBool default.isUnknown := by
      simp only [KleeneSignal.at, KleeneSignal.indicator, e1, e2, Kleene.ofBoolUnk]
    rw [this, Kleene.ofBoolUnk_toBool_isUnknown]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
