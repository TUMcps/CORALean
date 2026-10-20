module

public import CORALean.Specification.STL.Definitions.ReachSequence

@[expose] public section

/-!
# A disjunction over independent time blocks distributes over the traces

The gluing argument of the `∨`-distributivity in the proof of [1, Lemma 2]: when the parts `P i`
of a disjunction depend on the trace at pairwise disjoint sets of times, a reach sequence admits a
trace that falsifies all of them at once — each part's counterexample, glued — so `∀ξ ∃i` is `∃i
∀ξ`. Every `R t` must be non-empty, or `C(R)` is empty and the left side holds vacuously.

## Inputs
* `ι` – index type of the blocks
* `R` – reach sequence
* `T` – time set of each block
* `s` – chosen blocks
* `P` – property of each block

## Hypotheses
* `hne` – all reach sets are nonempty
* `hT` – the time sets of the chosen blocks are disjoint
* `hP` – each property depends only on its block

## Conclusion
* all traces satisfy some property iff some property holds for all traces

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSequence.forall_exists_iff_exists_forall {ι : Type} {R : ℝ≥0 → Set X}
    (hne : ∀ t, (R t).Nonempty) {T : ι → Set ℝ≥0} {s : Set ι}
    (hT : s.Pairwise fun a b => Disjoint (T a) (T b)) {P : ι → (ℝ≥0 → X) → Prop}
    (hP : ∀ i ξ ξ', (∀ x ∈ T i, ξ x = ξ' x) → (P i ξ ↔ P i ξ')) : -- --- CONCL ---
    (∀ ξ ∈ ReachSequence.traceSet R, ∃ i ∈ s, P i ξ) ↔
      ∃ i ∈ s, ∀ ξ ∈ ReachSequence.traceSet R, P i ξ := by -- --- PROOF ---
  classical
  refine ⟨fun h => ?_, fun ⟨i, hi, h⟩ ξ hξ => ⟨i, hi, h ξ hξ⟩⟩
  by_contra hcon
  push Not at hcon
  have : Nonempty (ℝ≥0 → X) := ⟨fun x => (hne x).some⟩
  -- every part has a counterexample trace in `C(R)`
  choose! f hfC hfP using hcon
  -- glue them: the trace is `f i` on the times of `i`, and anything elsewhere
  let ξ : ℝ≥0 → X := fun x =>
    if hx : ∃ i ∈ s, x ∈ T i then f hx.choose x else (hne x).some
  have hξ : ξ ∈ ReachSequence.traceSet R := by
    intro x
    by_cases hx : ∃ i ∈ s, x ∈ T i
    · simpa [ξ, hx] using hfC _ hx.choose_spec.1 x
    · simpa [ξ, hx] using (hne x).some_mem
  obtain ⟨i, hi, hPi⟩ := h ξ hξ
  refine hfP i hi ((hP i ξ (f i) fun x hx => ?_).1 hPi)
  -- on `T i` the glued trace is `f i`, the chosen part being `i` by disjointness
  have hx' : ∃ i ∈ s, x ∈ T i := ⟨i, hi, hx⟩
  simp only [ξ, hx', dite_true]
  obtain ⟨hi', hxi'⟩ := hx'.choose_spec
  by_cases hii : hx'.choose = i
  · rw [hii]
  · exact absurd hxi' (Set.disjoint_left.1 (hT hi' hi hii) |>.mt (not_not.2 hx))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
