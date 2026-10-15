module

public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorSpec
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# A Boolean signal embeds as a Kleene signal

`fromBoolSignal(bSig)` is valid and has, at every time, the Kleene value of the Boolean one.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.fromBoolSignal_spec
    (bSig : PointSegmentSignal ℝ) (hb : bSig.IsValid) :
    (KleeneSignal.fromBoolSignal bSig).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (KleeneSignal.fromBoolSignal bSig).at t = Kleene.fromBool (bSig.at t) := by -- --- PROOF ---
  obtain ⟨hv, hat⟩ := PointSegmentSignal.indicator_spec STLInterval.empty (fun f h => by cases h)
      false false
  refine ⟨⟨hb, hv⟩, fun t ht => ?_⟩
  have := (hat t ht).2 (by simp [STLInterval.set_empty])
  simp [KleeneSignal.at, KleeneSignal.fromBoolSignal, this]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
