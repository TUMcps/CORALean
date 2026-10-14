module

public import CORALean.Specification.FourValuedSignal.Theorems.IndicatorSpec
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# A uniform signal is constant

`uniformSignal(val)` is a valid signal with value `val` at every time.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.uniformSignal_spec
    (val : FourValued) :
    (FourValuedSignal.uniformSignal val : FourValuedSignal ℝ).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (FourValuedSignal.uniformSignal val : FourValuedSignal ℝ).at t = val := by
  obtain ⟨hv, hat⟩ := FourValuedSignal.indicator_spec STLInterval.empty (fun f h => by cases h)
      val val
  exact ⟨hv, fun t ht =>
    (hat t ht).2 (by simp [STLInterval.set_empty])⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
