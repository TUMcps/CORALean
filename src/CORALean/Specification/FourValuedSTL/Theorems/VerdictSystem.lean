module

public import CORALean.Specification.FourValuedSTL.Theorems.Verdict
public import Mathlib.Data.NNReal.Defs
public import CORALean.Specification.FourValuedSTL.Definitions.IsPartialAtomSignal

@[expose] public section

/-!
# The verdict on a system

Let `R̃` be a partial overapproximation of the reachable set of `H`, with an extension `R` that
covers every execution of `H` (`FourValuedSTL.exists_extension` gives one): then `⟦φ⟧_R̃(0) = ⊤`
implies `H ⊨ φ` ([1, Cor. 1]). `E` is the set of the executions of `H`, those of finite variability
that [1, Sec. 2.5] limits itself to.

The last sentence of [1, Cor. 1], "`⟦φ⟧_R̃(0) = ⊥` implies `H ⊭ φ`", needs an execution of `H`:
`H ⊭ φ` is `∃ ξ, ¬ ξ ⊨ φ`, which the covered executions all violating does not give for a system
with none (`FourValuedSTL.not_holdsOn_of_ff_counterexample`). It is proved here for `E` nonempty.

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

theorem FourValuedSTL.verdict_system {X : Type} (φ : FourValuedSTL.Formula X) (T : Set ℝ≥0)
    (Rp R : ℝ≥0 → Set X) (hext : FourValuedSTL.Extends R Rp T) (E : Set (ℝ≥0 → X))
    (hcov : ∀ ξ ∈ E, FourValuedSTL.Covers R ξ) (S : (X → Prop) → KleeneSignal ℝ)
    (S' : (X → Prop) → FourValuedSignal ℝ)
    (hS : ∀ a ∈ φ.atoms, FourValuedSTL.IsAtomSignal R a (S a))
    (hS' : ∀ a ∈ φ.atoms, FourValuedSTL.IsPartialAtomSignal T Rp a (S' a)) : -- --- STMT ---
    ∃ r, φ.fourValuedSat S' = some r ∧ r.IsValid ∧ (r.at 0 = FourValued.tt → φ.HoldsOn E) ∧
      (E.Nonempty → r.at 0 = FourValued.ff → ¬ φ.HoldsOn E) := by -- --- PROOF ---
  obtain ⟨r, hr, hv, h⟩ := FourValuedSTL.verdict φ T Rp R hext S S' hS hS'
  refine ⟨r, hr, hv, fun htt ξ hξ => (h ξ (hcov ξ hξ)).1 htt, ?_⟩
  -- an execution that exists violates `φ`, being covered
  rintro ⟨ξ, hξ⟩ hff hall
  exact (h ξ (hcov ξ hξ)).2 hff (hall ξ hξ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
