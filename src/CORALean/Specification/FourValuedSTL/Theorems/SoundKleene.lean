module

public import CORALean.Specification.FourValuedSTL.Operations.KleeneSat
public import CORALean.Specification.FourValuedSTL.Definitions.Basic
public import CORALean.Specification.FourValuedSTL.Theorems.HatSpec
public import CORALean.Specification.KleeneSignal.Theorems.AtAnd
public import CORALean.Specification.KleeneSignal.Theorems.UntilSpec
public import CORALean.Specification.KleeneSignal.Theorems.Basic
public import CORALean.Specification.KleeneSignal.Theorems.IndicatorSpec
public import CORALean.Specification.Kleene.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet
public import Mathlib.Data.NNReal.Defs
public import CORALean.Specification.FourValuedSTL.Definitions.Atoms

@[expose] public section

/-!
# Soundness of the three-valued semantics

For a reachable set `R` and every execution `ξ` covered by `R` (`ξ ≺ R`, `ξ(t) ∈ R(t)` for all `t`),
`⟦φ⟧_ξ ≺ ⟦φ⟧_R`: if `⟦φ⟧_R(t) = v ∈ B` then `⟦φ⟧_ξ(t) = v` ([1, Thm. 1]). The proof is the
paper's, by structural induction on `φ`, the inductive cases from the direct semantics of the
operators on `U₁`-signals (`KleeneSignal.at_not`, `at_and`, `until_spec`, [1, Eq. 2]); the step
for the until is the one that swaps an existential and a universal quantifier.

The satisfaction signal `⟦φ⟧_R` is built from the signals of the atoms, `S a` for `t ↦ â(R(t))`,
which must have finite variability (`FourValuedSTL.IsAtomSignal`): the operators of `U₁`-signals,
and the paper's until of Boolean signals under them, are defined for no other (`Lemma 2`).

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSTL.sound_kleene {X : Type} (φ : FourValuedSTL.Formula X) (R : ℝ≥0 → Set X)
    (S : (X → Prop) → KleeneSignal ℝ)
    (hS : ∀ a ∈ φ.atoms, FourValuedSTL.IsAtomSignal R a (S a))
    (ξ : ℝ≥0 → X) (hξ : FourValuedSTL.Covers R ξ) :
    (φ.kleeneSat S).IsValid ∧
      ∀ t : ℝ≥0, ((φ.kleeneSat S).at t).IsRefinedBy (φ.satBool ξ t) := by -- --- PROOF ---
  induction φ with
  | tt =>
    -- `true` is `True` everywhere
    obtain ⟨hv, h⟩ := KleeneSignal.indicator_spec STLInterval.empty .tt .tt
    refine ⟨hv, fun t => ?_⟩
    have := (h t t.2).2 (by simp [STLInterval.set_empty])
    simp only [FourValuedSTL.Formula.kleeneSat, this]
    rw [Kleene.isRefinedBy_iff_tt_ff]
    simp [FourValuedSTL.Formula.satBool, FourValuedSTL.Formula.Sat]
  | atom a =>
    -- an atom: `â(R(t)) = ⊤` gives `a(ξ(t))`, and `⊥` gives `¬a(ξ(t))`
    obtain ⟨hv, h⟩ := hS a (by simp [FourValuedSTL.Formula.atoms])
    refine ⟨hv, fun t => ?_⟩
    simp only [FourValuedSTL.Formula.kleeneSat, h t, FourValuedSTL.Formula.satBool,
      FourValuedSTL.Formula.Sat]
    rw [Kleene.isRefinedBy_iff_tt_ff]
    simpa using FourValuedSTL.hat_spec (hξ t)
  | not φ ih =>
    -- negation swaps `True` and `False`
    obtain ⟨hv, h⟩ := ih hS
    refine ⟨KleeneSignal.not_isValid _ hv, fun t => ?_⟩
    simp only [FourValuedSTL.Formula.kleeneSat]
    rw [KleeneSignal.at_not _ hv, Kleene.isRefinedBy_iff_tt_ff]
    have := (Kleene.isRefinedBy_iff_tt_ff _ _).1 (h t)
    simp only [FourValuedSTL.Formula.satBool, FourValuedSTL.Formula.Sat] at this ⊢
    generalize (φ.kleeneSat S).at t = k at this ⊢
    cases k <;> simp_all [Kleene.not]
  | and φ ψ ihφ ihψ =>
    -- conjunction: `True` if both are, `False` if one is, by the direct semantics
    obtain ⟨hv₁, h₁⟩ := ihφ (fun a ha => hS a (Or.inl ha))
    obtain ⟨hv₂, h₂⟩ := ihψ (fun a ha => hS a (Or.inr ha))
    obtain ⟨hv, h⟩ := KleeneSignal.at_and ![φ.kleeneSat S, ψ.kleeneSat S]
      (Fin.forall_fin_two.2 ⟨hv₁, hv₂⟩)
    refine ⟨hv, fun t => ?_⟩
    obtain ⟨htt, hff⟩ := h t t.2
    simp only [Fin.forall_fin_two, Fin.exists_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at htt hff
    simp only [FourValuedSTL.Formula.kleeneSat]
    rw [Kleene.isRefinedBy_iff_tt_ff, htt, hff]
    have a1 := (Kleene.isRefinedBy_iff_tt_ff _ _).1 (h₁ t)
    have a2 := (Kleene.isRefinedBy_iff_tt_ff _ _).1 (h₂ t)
    simp only [FourValuedSTL.Formula.satBool, FourValuedSTL.Formula.Sat, decide_eq_true_eq,
      decide_eq_false_iff_not] at a1 a2 ⊢
    constructor
    · exact fun h => ⟨a1.1 h.1, a2.1 h.2⟩
    · rintro (h | h)
      · exact fun hh => a1.2 h hh.1
      · exact fun hh => a2.2 h hh.2
  | «until» I φ ψ ihφ ihψ =>
    -- until: the witness `t'` of the `U₁`-semantics is one for every covered execution
    obtain ⟨hv₁, h₁⟩ := ihφ (fun a ha => hS a (Or.inl ha))
    obtain ⟨hv₂, h₂⟩ := ihψ (fun a ha => hS a (Or.inr ha))
    obtain ⟨hv, h⟩ := KleeneSignal.until_spec _ _ hv₁ hv₂ I
    refine ⟨hv, fun t => ?_⟩
    obtain ⟨htt, hff⟩ := h t t.2
    simp only [FourValuedSTL.Formula.kleeneSat]
    rw [Kleene.isRefinedBy_iff_tt_ff, htt, hff]
    have a1 := fun t => (Kleene.isRefinedBy_iff_tt_ff _ _).1 (h₁ t)
    have a2 := fun t => (Kleene.isRefinedBy_iff_tt_ff _ _).1 (h₂ t)
    simp only [FourValuedSTL.Formula.satBool, FourValuedSTL.Formula.Sat, decide_eq_true_eq,
      decide_eq_false_iff_not] at a1 a2 ⊢
    constructor
    -- `True`: the witness `t'` is a time of `ℝ≥0`, since `I` is over `ℝ≥0`
    · rintro ⟨t', hu, hr, hl⟩
      have hd := STLInterval.zero_le_of_mem_set I _ hu
      have ht' : 0 ≤ t' := by have := NNReal.coe_nonneg t; linarith
      refine ⟨⟨t', ht'⟩, hu, (a2 ⟨t', ht'⟩).1 hr, fun t'' h1 h2 => (a1 t'').1 (hl t'' ?_ ?_)⟩
      · exact_mod_cast h1
      · exact_mod_cast h2
    -- `False`: a witness of `Sat` is a time where `ψ` is not `False` and `φ` not `False` before
    · intro H ⟨t', hu, hr, hl⟩
      rcases H t' hu with h0 | ⟨x, hx1, hx2, hx3⟩
      · exact (a2 t').2 h0 hr
      · have hx0 : 0 ≤ x := by have := NNReal.coe_nonneg t; linarith
        exact (a1 ⟨x, hx0⟩).2 hx3 (hl ⟨x, hx0⟩ (by exact_mod_cast hx1) (by exact_mod_cast hx2))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
