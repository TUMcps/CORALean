module

public import CORALean.Specification.FourValuedSTL.Theorems.SoundKleene
public import CORALean.Specification.FourValuedSTL.Theorems.SoundFourValued
public import Mathlib.Data.NNReal.Defs
public import CORALean.Specification.FourValuedSTL.Definitions.IsPartialAtomSignal

@[expose] public section

/-!
# The verdict on the covered executions

Let `R̃` be a partial reachable set and `R` an extension of it ([1, Cor. 1]). If `⟦φ⟧_R̃(0)` is `⊤`,
every execution `ξ` covered by `R` satisfies `φ` (`ξ ⊨ φ`, `⟦φ⟧_ξ(0) = ⊤`), and if it is `⊥`, none
does. A value `⊣₁` or `⊣₂` says no more than "unknown" and "inconclusive": the corollary makes no
claim in these cases, and `⟦φ⟧_R̃(0)` is `⊣₂` exactly when `R̃` leaves it open. The proof is
[1, Thm. 2] (`⟦φ⟧_R ≺ ⟦φ⟧_R̃`) and then [1, Thm. 1] (`⟦φ⟧_ξ ≺ ⟦φ⟧_R`).

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

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSTL.verdict {X : Type} (φ : FourValuedSTL.Formula X) (T : Set ℝ≥0)
    (Rp R : ℝ≥0 → Set X) (hext : FourValuedSTL.Extends R Rp T)
    (S : (X → Prop) → KleeneSignal ℝ) (S' : (X → Prop) → FourValuedSignal ℝ)
    (hS : ∀ a ∈ φ.atoms, FourValuedSTL.IsAtomSignal R a (S a))
    (hS' : ∀ a ∈ φ.atoms, FourValuedSTL.IsPartialAtomSignal T Rp a (S' a)) : -- --- CONCL ---
    ∃ r, φ.fourValuedSat S' = some r ∧ r.IsValid ∧ ∀ ξ : ℝ≥0 → X, FourValuedSTL.Covers R ξ →
      (r.at 0 = FourValued.tt → φ.Sat ξ 0) ∧
        (r.at 0 = FourValued.ff → ¬ φ.Sat ξ 0) := by -- --- PROOF ---
  obtain ⟨r, hr, hv, h⟩ := FourValuedSTL.sound_fourValued φ T Rp R hext S S' hS hS'
  refine ⟨r, hr, hv, fun ξ hξ => ?_⟩
  -- the refinement chain `⟦φ⟧_ξ ≺ ⟦φ⟧_R ≺ ⟦φ⟧_R̃` at time `0`
  have h1 := (Kleene.isRefinedBy_iff_tt_ff _ _).1
    ((FourValuedSTL.sound_kleene φ R S hS ξ hξ).2 0)
  have h2 := h 0 le_rfl
  simp only [FourValuedSTL.Formula.satBool, decide_eq_true_eq, decide_eq_false_iff_not,
    NNReal.coe_zero] at h1 h2
  constructor
  · intro htt
    refine h1.1 ?_
    have := h2 (by rw [htt]; simp)
    rw [htt] at this
    exact (FourValued.fromKleene_eq_tt_iff _).1 this
  · intro hff
    refine h1.2 ?_
    have := h2 (by rw [hff]; simp)
    rw [hff] at this
    exact (FourValued.fromKleene_eq_ff_iff _).1 this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
