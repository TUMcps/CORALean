module

public import CORALean.Specification.KleeneSignal.Theorems.AtAnd
public import CORALean.Specification.Kleene.Instances
public import CORALean.Specification.Kleene.Theorems.Basic

@[expose] public section

/-!
# The conjunction of three-valued signals is monotone

If every `Λₖ ⊑ₜ Λₖ'` at every time `t ≥ 0`, then `⋀ Λₖ ⊑ₜ ⋀ Λₖ'` there: `∧` on `U₁`-signals is
monotone ([1, Lemma 3]), proved from the direct semantics of [1, Eq. 2] (`at_and`).

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

theorem KleeneSignal.and_mono {ι : Type} [Fintype ι] [Nonempty ι]
    (sigs sigs' : ι → KleeneSignal ℝ) (hv : ∀ k, (sigs k).IsValid) (hv' : ∀ k, (sigs' k).IsValid)
    (h : ∀ k, ∀ t : ℝ, 0 ≤ t → (sigs k).at t ≤ (sigs' k).at t) :
    ∀ t : ℝ, 0 ≤ t →
      (KleeneSignal.and_ sigs).at t ≤ (KleeneSignal.and_ sigs').at t := by -- --- PROOF ---
  intro t ht
  obtain ⟨-, a⟩ := KleeneSignal.at_and sigs hv
  obtain ⟨-, a'⟩ := KleeneSignal.at_and sigs' hv'
  rw [Kleene.le_iff_tt_ff]
  refine ⟨fun htt => ?_, fun hff => ?_⟩
  · rw [(a' t ht).1]
    intro k
    have := ((a t ht).1.1 htt) k
    exact (Kleene.le_iff_tt_ff _ _).1 (h k t ht) |>.1 this
  · obtain ⟨k, hk⟩ := (a' t ht).2.1 hff
    exact (a t ht).2.2 ⟨k, (Kleene.le_iff_tt_ff _ _).1 (h k t ht) |>.2 hk⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
