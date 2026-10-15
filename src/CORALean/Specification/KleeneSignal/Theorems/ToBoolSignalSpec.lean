module

public import CORALean.Specification.Kleene.Theorems.Basic
public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Operations.ToBoolSignal
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsSpec
public import CORALean.Specification.Theorems.FoldlSetSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.SetSpec

@[expose] public section

/-!
# Mapping the unknown values of a three-valued signal

For a valid three-valued signal, `toBoolSignal(obj,mapUnknownTo)` is valid and has the value
`mapUnknownTo` at every time `t ≥ 0` where the signal is unknown, and the Boolean value of the
signal elsewhere.

With `false` and `true` this is the underapproximation `⌊Λ⌋` and the overapproximation `⌈Λ⌉` of
[1, Sec. 4.2 (refinements)].

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

/-- The unknown values become `mapUnknownTo`, the others stay. -/
theorem KleeneSignal.toBoolSignal_spec (s : KleeneSignal ℝ) (hs : s.IsValid) (v : Bool) :
    (s.toBoolSignal v).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (s.at t = Kleene.uu → (s.toBoolSignal v).at t = v) ∧
      (s.at t ≠ Kleene.uu → (s.toBoolSignal v).at t = (s.at t).toBool) := by -- --- PROOF ---
  obtain ⟨h0, h1, -⟩ := s.isUnknown.findIntervals_spec hs.2 id
  -- the intervals are set in turn
  obtain ⟨hv, h2⟩ := List.foldl_set_spec (fun sig : PointSegmentSignal ℝ => sig.IsValid)
    (fun sig t => sig.at t) (s.isUnknown.findIntervals) (fun I => I.set) v
    (fun sig I => sig.set I v)
    (fun sig I hI hsig => by
      obtain ⟨hv, h⟩ := PointSegmentSignal.set_spec sig hsig I (h0 I hI) v
      exact ⟨hv, fun t ht => h t ht⟩) s.signal hs.1
  refine ⟨hv, fun t ht => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · -- unknown: the time is in an interval
    have hun : s.isUnknown.at t = true := by
      by_contra h; simp [KleeneSignal.at, h, Kleene.fromBool] at hu; split_ifs at hu
    unfold KleeneSignal.toBoolSignal
    exact (h2 t ht).1 (by simpa using (h1 t ht).2 hun)
  · -- known: the time is in no interval
    have hun : s.isUnknown.at t = false := by
      by_contra h
      have h' : s.isUnknown.at t = true := by simpa using h
      simp [KleeneSignal.at, h'] at hu
    have hno : ¬ ∃ I ∈ s.isUnknown.findIntervals, t ∈ I.set := by
      intro h; have := (h1 t ht).1 (by simpa using h); simp [hun] at this
    unfold KleeneSignal.toBoolSignal
    rw [(h2 t ht).2 hno]
    simp only [KleeneSignal.at, hun, Bool.false_eq_true, if_false]
    cases s.signal.at t <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
