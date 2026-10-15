module

public import CORALean.Specification.FourValued.Theorems.Basic
public import CORALean.Specification.FourValuedSignal.Operations.ToKleeneSignal
public import CORALean.Specification.FourValuedSignal.Theorems.Basic
public import CORALean.Specification.KleeneSignal.Theorems.SetSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsSpec
public import CORALean.Specification.Theorems.FoldlSetSpec

@[expose] public section

/-!
# Mapping the inconclusive values of a four-valued signal

For a valid four-valued signal, `toKleeneSignal(obj,mapInconclusiveTo)` is valid and has the value
`mapInconclusiveTo` at every time `t ≥ 0` where the signal is inconclusive, and the Kleene value of
the signal elsewhere.

With `False` and `True` this is the underapproximation `⌊Λ̃⌋` and the overapproximation `⌈Λ̃⌉` of
[1, Sec. 4.3 (refinements)].

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The inconclusive values become `mapInconclusiveTo`, the others stay. -/
theorem FourValuedSignal.toKleeneSignal_spec (s : FourValuedSignal ℝ) (hs : s.IsValid)
    (v : Kleene) : (s.toKleeneSignal v).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (s.at t = FourValued.ii → (s.toKleeneSignal v).at t = v) ∧
      (s.at t ≠ FourValued.ii →
        (s.toKleeneSignal v).at t = (s.at t).toKleene) := by -- --- PROOF ---
  obtain ⟨h0, h1, -⟩ := s.isInconclusive.findIntervals_spec hs.2 id
  -- the intervals are set in turn
  obtain ⟨hv, h2⟩ := List.foldl_set_spec (fun sig : KleeneSignal ℝ => sig.IsValid)
    (fun sig t => sig.at t) (s.isInconclusive.findIntervals) (fun I => I.set) v
    (fun sig I => sig.set I v)
    (fun sig I hI hsig => by
      obtain ⟨hv, h⟩ := KleeneSignal.set_spec sig hsig I (h0 I hI) v
      exact ⟨hv, fun t ht => h t ht⟩) s.signal hs.1
  have hcond : ∀ t : ℝ, 0 ≤ t → ((∃ I ∈ s.isInconclusive.findIntervals, t ∈ I.set) ↔
      s.isInconclusive.at t = true) := fun t ht => by simpa using h1 t ht
  refine ⟨hv, fun t ht => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · -- inconclusive: the time is in an interval
    unfold FourValuedSignal.toKleeneSignal
    exact (h2 t ht).1 ((hcond t ht).2 ((FourValuedSignal.at_eq_ii_iff s t).1 hu))
  · -- conclusive: the time is in no interval
    have hun : s.isInconclusive.at t = false := by
      by_contra h
      exact hu ((FourValuedSignal.at_eq_ii_iff s t).2 (by simpa using h))
    have hno : ¬ ∃ I ∈ s.isInconclusive.findIntervals, t ∈ I.set := by
      intro h; have := (hcond t ht).1 h; simp [hun] at this
    unfold FourValuedSignal.toKleeneSignal
    rw [(h2 t ht).2 hno]
    simp only [FourValuedSignal.at, hun, Bool.false_eq_true, if_false]
    cases s.signal.at t <;> rfl
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
