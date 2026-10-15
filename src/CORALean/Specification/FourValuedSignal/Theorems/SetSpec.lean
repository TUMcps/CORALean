module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Theorems.SetSpec
public import CORALean.Specification.FourValued.Theorems.Basic

@[expose] public section

/-!
# Setting a time interval of a four-valued signal

For a valid signal, `set(obj,interval,value)` is valid and has `value` at the times of the interval
and the signal's own value elsewhere: the Kleene part and the inconclusive part are set to the
parts of `value`, and a value is recovered from its parts.

This is `Set(c.irr, ⊣₂)` in line 12 of [1, Alg. 2], which drops the irrelevant prefix of a child.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.set_spec (s : FourValuedSignal ℝ)
    (hs : s.IsValid) (I : STLInterval) (value :
        FourValued) :
    (s.set I value).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (s.set I value).at t = value) ∧
      (t ∉ I.set → (s.set I value).at t = s.at t) := by -- --- PROOF ---
  obtain ⟨hv1, h1⟩ := KleeneSignal.set_spec s.signal hs.1 I value.toKleene
  obtain ⟨hv2, h2⟩ := PointSegmentSignal.set_spec s.isInconclusive hs.2 I value.isInconclusive
  refine ⟨⟨hv1, hv2⟩, fun t ht => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · -- inside: the value is `value`, rebuilt from its parts
    have : (s.set I value).at t = FourValued.ofKleeneInc value.toKleene value.isInconclusive := by
      simp only [FourValuedSignal.at, FourValuedSignal.set, (h1 t ht).1 hm, (h2 t ht).1 hm,
        FourValued.ofKleeneInc]
    rw [this, FourValued.ofKleeneInc_toKleene_isInconclusive]
  · -- outside: both parts are the old ones
    simp only [FourValuedSignal.at, FourValuedSignal.set, (h1 t ht).2 hm, (h2 t ht).2 hm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
