module

public import CORALean.Specification.FourValuedSTL.Operations.KleeneSat
public import CORALean.Specification.FourValuedSTL.Definitions.Basic
public import CORALean.Specification.KleeneSignal.Theorems.AtAnd
public import CORALean.Specification.KleeneSignal.Theorems.UntilSpec
public import CORALean.Specification.KleeneSignal.Theorems.Basic
public import CORALean.Specification.KleeneSignal.Theorems.IndicatorSpec
public import Mathlib.Data.NNReal.Defs
public import CORALean.Specification.FourValuedSTL.Definitions.Atoms

@[expose] public section

/-!
# The three-valued satisfaction signal is valid

If the signals of the atoms of `φ` are valid, so is `⟦φ⟧_R` of [1, Sec. 4.2 (satisfaction)]: the
operators of `U₁`-signals keep a signal of finite variability (`KleeneSignal.not_isValid`,
`at_and`, `until_spec`), as does `true`.

## Inputs
* `X` – state type
* `φ` – formula
* `S` – three-valued signal of each atom

## Hypotheses
* `hS` – the signals of the formula's atoms are valid

## Conclusion
* the three-valued satisfaction signal is valid

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSTL.kleeneSat_isValid {X : Type} (φ : FourValuedSTL.Formula X)
    (S : (X → Prop) → KleeneSignal ℝ) (hS : ∀ a ∈ φ.atoms, (S a).IsValid) : -- --- CONCL ---
    (φ.kleeneSat S).IsValid := by -- --- PROOF ---
  induction φ with
  | tt => exact (KleeneSignal.indicator_spec STLInterval.empty .tt .tt).1
  | atom a => exact hS a (by simp [FourValuedSTL.Formula.atoms])
  | not φ ih => exact KleeneSignal.not_isValid _ (ih hS)
  | and φ ψ ihφ ihψ =>
    exact (KleeneSignal.at_and ![φ.kleeneSat S, ψ.kleeneSat S]
      (Fin.forall_fin_two.2 ⟨ihφ fun a ha => hS a (Or.inl ha),
        ihψ fun a ha => hS a (Or.inr ha)⟩)).1
  | «until» I φ ψ ihφ ihψ =>
    exact (KleeneSignal.until_spec _ _ (ihφ fun a ha => hS a (Or.inl ha))
      (ihψ fun a ha => hS a (Or.inr ha)) I).1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
