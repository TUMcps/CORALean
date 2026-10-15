module

public import CORALean.Specification.PointSegmentSignal.Theorems.SetSpec
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic

@[expose] public section

/-!
# Invalidating a time interval

`setInvalid(obj,interval)` of a valid signal is valid, `Inconclusive` at the times of the interval
and unchanged elsewhere: neither value can hold on the interval.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem TentativeKleeneSignal.setInvalid_spec (s : TentativeKleeneSignal ℝ) (hs : s.IsValid)
    (I : STLInterval) (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) :
    (s.setInvalid I).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (s.setInvalid I).at t = FourValued.ii) ∧
      (t ∉ I.set → (s.setInvalid I).at t = s.at t) := by -- --- PROOF ---
  obtain ⟨hv1, h1⟩ := PointSegmentSignal.set_spec s.canBeTrue hs.1 I hI false
  obtain ⟨hv2, h2⟩ := PointSegmentSignal.set_spec s.canBeFalse hs.2 I hI false
  refine ⟨⟨hv1, hv2⟩, fun t ht => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · simp only [TentativeKleeneSignal.at, TentativeKleeneSignal.setInvalid, (h1 t ht).1 hm,
      (h2 t ht).1 hm]
  · simp only [TentativeKleeneSignal.at, TentativeKleeneSignal.setInvalid, (h1 t ht).2 hm,
      (h2 t ht).2 hm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
