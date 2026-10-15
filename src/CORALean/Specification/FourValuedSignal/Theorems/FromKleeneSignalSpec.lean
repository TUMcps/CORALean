module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorSpec
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# A Kleene signal embeds as a four-valued signal

`fromKleeneSignal(kSig)` is valid and has, at every time, the four-valued value of the Kleene one.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.fromKleeneSignal_spec
    (kSig : KleeneSignal ℝ) (hk : kSig.IsValid) :
    (FourValuedSignal.fromKleeneSignal kSig).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (FourValuedSignal.fromKleeneSignal kSig).at t =
        FourValued.fromKleene (kSig.at t) := by -- --- PROOF ---
  obtain ⟨hv, hat⟩ := PointSegmentSignal.indicator_spec STLInterval.empty false false
  refine ⟨⟨hk, hv⟩, fun t ht => ?_⟩
  have := (hat t ht).2 (by simp [STLInterval.set_empty])
  simp [FourValuedSignal.at, FourValuedSignal.fromKleeneSignal, this]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
