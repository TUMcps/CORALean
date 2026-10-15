module

public import CORALean.Specification.FourValuedSTL.Operations.FourValuedSat
public import CORALean.Specification.FourValuedSTL.Theorems.KleeneSatIsValid
public import CORALean.Specification.FourValuedSignal.Theorems.NotIsRefinedBy
public import CORALean.Specification.FourValuedSignal.Theorems.AndIsRefinedBy
public import CORALean.Specification.FourValuedSignal.Theorems.UntilIsRefinedBy
public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.KleeneSignal.Theorems.IndicatorSpec
public import Mathlib.Data.NNReal.Defs
public import CORALean.Specification.FourValuedSTL.Definitions.Atoms
public import CORALean.Specification.FourValuedSTL.Definitions.IsPartialAtomSignal
public import CORALean.Specification.FourValuedSTL.Definitions.Basic

@[expose] public section

/-!
# Soundness of the four-valued semantics

For a partial reachable set `R̃ : T → 2^X` and every reachable set `R` that extends it (`R ≺ R̃`,
`R(t) = R̃(t)` on `T`), `⟦φ⟧_R ≺ ⟦φ⟧_R̃`: if `⟦φ⟧_R̃(t) = v ∈ U₁` then `⟦φ⟧_R(t) = v`
([1, Thm. 2]). The paper sketches the proof as the one of [1, Thm. 1] with a direct semantics of
the operators of `U₂`-signals; here the inductive cases are the three lemmas that each operator of
`U₂`-signals respects refinement (`FourValuedSignal.not_isRefinedBy`, `and_isRefinedBy`,
`until_isRefinedBy`), the
last from the monotonicity of [1, Lemma 3] that [1, Sec. 4.3 (operators)] defines the operators by.

The signals of the atoms are given and valid, as for [1, Thm. 1] (`FourValuedSTL.IsAtomSignal`,
`IsPartialAtomSignal`): finite variability, which the paper does not ask of `R` and `R̃`.

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

theorem FourValuedSTL.sound_fourValued {X : Type} (φ : FourValuedSTL.Formula X) (T : Set ℝ≥0)
    (Rp R : ℝ≥0 → Set X) (hext : FourValuedSTL.Extends R Rp T)
    (S : (X → Prop) → KleeneSignal ℝ) (S' : (X → Prop) → FourValuedSignal ℝ)
    (hS : ∀ a ∈ φ.atoms, FourValuedSTL.IsAtomSignal R a (S a))
    (hS' : ∀ a ∈ φ.atoms, FourValuedSTL.IsPartialAtomSignal T Rp a (S' a)) :
    ∃ r, φ.fourValuedSat S' = some r ∧ r.IsValid ∧
      r.IsRefinedBy (φ.kleeneSat S) := by -- --- PROOF ---
  classical
  induction φ with
  | tt =>
    -- `true` is `True` in both
    obtain ⟨hv, h⟩ := FourValuedSignal.uniformSignal_spec FourValued.tt
    obtain ⟨hv', h'⟩ := KleeneSignal.indicator_spec STLInterval.empty (fun f h => by cases h)
      .tt .tt
    refine ⟨_, rfl, hv, fun t ht => ?_⟩
    simp only [FourValuedSTL.Formula.kleeneSat]
    rw [h t ht, (h' t ht).2 (by simp [STLInterval.set_empty])]
    intro _
    rfl
  | atom a =>
    -- an atom: where `R̃` is known the two signals agree, elsewhere the value is ⊣₂
    obtain ⟨hv, h⟩ := hS' a (by simp [FourValuedSTL.Formula.atoms])
    obtain ⟨-, h2⟩ := hS a (by simp [FourValuedSTL.Formula.atoms])
    refine ⟨_, rfl, hv, fun t ht => ?_⟩
    have hc : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
    simp only [FourValuedSTL.Formula.kleeneSat]
    rw [← hc, h, h2]
    by_cases hT : t.toNNReal ∈ T
    · rw [if_pos hT, hext _ hT]
      intro _
      rfl
    · rw [if_neg hT]
      exact fun hh => absurd rfl hh
  | not φ ih =>
    -- negation respects refinement
    obtain ⟨r, hr, hv, h⟩ := ih (fun a ha => hS a ha) (fun a ha => hS' a ha)
    refine ⟨r.not, by simp [FourValuedSTL.Formula.fourValuedSat, hr],
      FourValuedSignal.not_isValid _ hv, ?_⟩
    exact FourValuedSignal.not_isRefinedBy r _ hv (FourValuedSTL.kleeneSat_isValid φ S
      fun a ha => (hS a ha).1) h
  | and φ ψ ihφ ihψ =>
    -- so does conjunction, by the direct semantics
    obtain ⟨r₁, hr₁, hv₁, h₁⟩ := ihφ (fun a ha => hS a (Or.inl ha))
      (fun a ha => hS' a (Or.inl ha))
    obtain ⟨r₂, hr₂, hv₂, h₂⟩ := ihψ (fun a ha => hS a (Or.inr ha))
      (fun a ha => hS' a (Or.inr ha))
    obtain ⟨r, hr, hv, h⟩ := FourValuedSignal.and_isRefinedBy ![r₁, r₂]
      ![φ.kleeneSat S, ψ.kleeneSat S] (Fin.forall_fin_two.2 ⟨hv₁, hv₂⟩)
      (Fin.forall_fin_two.2 ⟨FourValuedSTL.kleeneSat_isValid φ S fun a ha => (hS a (Or.inl ha)).1,
        FourValuedSTL.kleeneSat_isValid ψ S fun a ha => (hS a (Or.inr ha)).1⟩)
      (Fin.forall_fin_two.2 ⟨h₁, h₂⟩)
    exact ⟨r, by simp [FourValuedSTL.Formula.fourValuedSat, hr₁, hr₂, hr], hv, h⟩
  | «until» I hI φ ψ ihφ ihψ =>
    -- and the until, by the monotonicity of [1, Lemma 3]
    obtain ⟨r₁, hr₁, hv₁, h₁⟩ := ihφ (fun a ha => hS a (Or.inl ha))
      (fun a ha => hS' a (Or.inl ha))
    obtain ⟨r₂, hr₂, hv₂, h₂⟩ := ihψ (fun a ha => hS a (Or.inr ha))
      (fun a ha => hS' a (Or.inr ha))
    obtain ⟨r, hr, hv, h⟩ := FourValuedSignal.until_isRefinedBy r₁ r₂ _ _ hv₁ hv₂
      (FourValuedSTL.kleeneSat_isValid φ S fun a ha => (hS a (Or.inl ha)).1)
      (FourValuedSTL.kleeneSat_isValid ψ S fun a ha => (hS a (Or.inr ha)).1) h₁ h₂ I hI
    exact ⟨r, by simp [FourValuedSTL.Formula.fourValuedSat, hr₁, hr₂, hr], hv, h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
