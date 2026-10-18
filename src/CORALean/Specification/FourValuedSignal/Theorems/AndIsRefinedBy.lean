module

public import CORALean.Specification.FourValuedSignal.Theorems.AtAnd
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalAt

@[expose] public section

/-!
# The conjunction of four-valued signals respects refinement

If the Kleene signals `Λₖ` refine the four-valued `Λ̃ₖ` (`Λₖ ≺ Λ̃ₖ`), then `⋀ Λₖ ≺ ⋀ Λ̃ₖ`: the step
of the induction in [1, Thm. 2] for `∧`. Proved from the direct semantics of `∧` on `U₂`-signals
(`at_and`), the pattern of [1, Eq. 2] [1, Sec. 4.3 (operators)] describes.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.and_isRefinedBy {ι : Type} [Fintype ι] [Nonempty ι]
    (sigs : ι → FourValuedSignal ℝ) (ks : ι → KleeneSignal ℝ) (hs : ∀ i, (sigs i).IsValid)
    (hk : ∀ i, (ks i).IsValid) (h : ∀ i, (sigs i).IsRefinedBy (ks i)) : -- --- STMT ---
    ∃ r, FourValuedSignal.and_ sigs = some r ∧ r.IsValid ∧
      r.IsRefinedBy (KleeneSignal.and_ ks) := by -- --- PROOF ---
  obtain ⟨r, hr, hv, hc⟩ := FourValuedSignal.at_and sigs hs
  obtain ⟨-, hkc⟩ := KleeneSignal.at_and ks hk
  refine ⟨r, hr, hv, fun t ht => ?_⟩
  obtain ⟨c1, c2, c3⟩ := hc t ht
  obtain ⟨d1, d2⟩ := hkc t ht
  intro hne
  have hr' : ∀ i, (sigs i).at t ≠ FourValued.ii →
      FourValued.fromKleene ((ks i).at t) = (sigs i).at t := fun i => h i t ht
  -- the value of the conjunction of the refinements, by the cases of the four-valued one
  generalize hK : (KleeneSignal.and_ ks).at t = K at d1 d2 ⊢
  generalize hV : r.at t = V at c1 c2 c3 hne ⊢
  cases V
  · -- `False`: some signal is `False`, hence so is its refinement
    obtain ⟨i, hi⟩ := c2.1 rfl
    have := hr' i (by rw [hi]; simp)
    rw [hi] at this
    have hki : (ks i).at t = Kleene.ff := (FourValued.fromKleene_eq_ff_iff _).1 this
    have := d2.2 ⟨i, hki⟩
    rw [this]; rfl
  · -- `Unknown`: no signal is `False` or `Inconclusive`, and not all are `True`
    have hnf : ∀ i, (sigs i).at t ≠ FourValued.ff := fun i hi => by
      have := c2.2 ⟨i, hi⟩; simp at this
    have hni : ∀ i, (sigs i).at t ≠ FourValued.ii := fun i hi => by
      have := c3.2 ⟨hnf, i, hi⟩; simp at this
    have hnt : ¬ ∀ i, (sigs i).at t = FourValued.tt := fun hh => by
      have := c1.2 hh; simp at this
    -- the refinements are then neither all `True` nor one `False`
    have hK1 : K ≠ Kleene.tt := fun hKt => by
      refine hnt fun i => ?_
      have := (d1.1 hKt) i
      have h2 := hr' i (hni i)
      rw [this] at h2
      exact h2.symm
    have hK2 : K ≠ Kleene.ff := fun hKf => by
      obtain ⟨i, hi⟩ := d2.1 hKf
      have h2 := hr' i (hni i)
      rw [hi] at h2
      exact hnf i h2.symm
    cases K
    · exact absurd rfl hK2
    · rfl
    · exact absurd rfl hK1
  · exact absurd rfl hne
  · -- `True`: all signals are `True`, and so are their refinements
    have hK : K = Kleene.tt := d1.2 fun i => by
      have h2 := hr' i (by rw [c1.1 rfl i]; simp)
      rw [c1.1 rfl i] at h2
      exact (FourValued.fromKleene_eq_tt_iff _).1 h2
    rw [hK]; rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
