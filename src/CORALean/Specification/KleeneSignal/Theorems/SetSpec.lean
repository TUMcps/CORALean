module

public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.SetSpec
public import CORALean.Specification.Kleene.Theorems.Basic

@[expose] public section

/-!
# Setting a time interval of a Kleene signal

For a valid signal, `set(obj,interval,value)` is valid and has `value` at the times of the interval
and the signal's own value elsewhere: both parts are set to the parts of `value`, and a value is
recovered from its parts.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.set_spec (s : KleeneSignal ℝ)
    (hs : s.IsValid) (I : STLInterval) (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) (value :
        Kleene) :
    (s.set I value).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (s.set I value).at t = value) ∧
      (t ∉ I.set → (s.set I value).at t = s.at t) := by -- --- PROOF ---
  obtain ⟨hv1, h1⟩ := PointSegmentSignal.set_spec s.signal hs.1 I hI value.toBool
  obtain ⟨hv2, h2⟩ := PointSegmentSignal.set_spec s.isUnknown hs.2 I hI value.isUnknown
  refine ⟨⟨hv1, hv2⟩, fun t ht => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · -- inside: the value is `value`, rebuilt from its parts
    have : (s.set I value).at t = Kleene.ofBoolUnk value.toBool value.isUnknown := by
      simp only [KleeneSignal.at, KleeneSignal.set, (h1 t ht).1 hm, (h2 t ht).1 hm,
        Kleene.ofBoolUnk]
    rw [this, Kleene.ofBoolUnk_toBool_isUnknown]
  · -- outside: both parts are the old ones
    simp only [KleeneSignal.at, KleeneSignal.set, (h1 t ht).2 hm, (h2 t ht).2 hm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
