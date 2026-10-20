module

public import CORALean.Specification.STL.Definitions.CDivisibleFormula
public import CORALean.Specification.STL.Operations.NnfToFormula
public import CORALean.Specification.STL.Operations.FormulaScale
public import CORALean.Specification.STL.Theorems.ScaleOfPform
public import CORALean.Specification.STL.Theorems.SatOfPform
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatOr
public import CORALean.Specification.STL.Theorems.SatRelease

@[expose] public section

/-!
# A c-divisible STL formula is a scaled normal form

[1, Lemma 4]: "without loss of generality, we assume that `ϕ` is in negation normal form". A
`c`-divisible STL formula has a normal form with natural bounds, scaled by `c`, and so has its
negation: `¬(φ U ψ) ≡ ¬φ R ¬ψ`, `¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ`.

## Inputs
* `c` – time step
* `φ` – formula

## Hypotheses
* `hstl` – the formula uses only the operators of STL
* `hdiv` – the formula is divisible by the step

## Conclusion
* the formula and its negation are scaled normal forms

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

theorem STL.Formula.exists_nnf (c : ℝ≥0) (φ : STL.Formula X) (hstl : φ.IsStl)
    (hdiv : φ.CDivisible c) : ∃ n n' : STL.Nnf X,
      (∀ ξ, (n.toFormula.scale c).Sat ξ ↔ φ.Sat ξ) ∧
        ∀ ξ, (n'.toFormula.scale c).Sat ξ ↔ ¬ φ.Sat ξ := by -- --- PROOF ---
  induction φ with
  | atom p =>
    refine ⟨.lit (.atom p), .lit (.not (.atom p)), fun ξ => ?_, fun ξ => ?_⟩ <;>
      simp only [STL.Nnf.toFormula, STL.Formula.scale_ofPform, STL.Formula.sat_ofPform] <;> rfl
  | not φ ih =>
    obtain ⟨n, n', h, h'⟩ := ih hstl hdiv
    exact ⟨n', n, h', fun ξ => (h ξ).trans not_not.symm⟩
  | or φ ψ ihφ ihψ =>
    obtain ⟨n₁, n₁', h₁, h₁'⟩ := ihφ hstl.1 hdiv.1
    obtain ⟨n₂, n₂', h₂, h₂'⟩ := ihψ hstl.2 hdiv.2
    refine ⟨.or n₁ n₂, .and n₁' n₂', fun ξ => ?_, fun ξ => ?_⟩
    · -- `∨` is `∨`
      simp only [STL.Nnf.toFormula, STL.Formula.scale, STL.Formula.sat_or, h₁, h₂]
    · -- `¬(φ ∨ ψ)` is `¬φ ∧ ¬ψ`
      show (STL.Formula.and (n₁'.toFormula.scale c) (n₂'.toFormula.scale c)).Sat ξ ↔
        ¬ (φ.Sat ξ ∨ ψ.Sat ξ)
      rw [STL.Formula.sat_and, h₁' ξ, h₂' ξ]
      exact not_or.symm
  | «until» a b φ ψ ihφ ihψ =>
    obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩, hφ, hψ⟩ := hdiv
    obtain ⟨n₁, n₁', h₁, h₁'⟩ := ihφ hstl.1 hφ
    obtain ⟨n₂, n₂', h₂, h₂'⟩ := ihψ hstl.2 hψ
    refine ⟨.until i j n₁ n₂, .release i j n₁' n₂', fun ξ => ?_, fun ξ => ?_⟩
    · -- the same window, with the operands replaced by equivalent ones
      simp only [STL.Nnf.toFormula, STL.Formula.scale, STL.Formula.Sat, h₁, h₂]
    · -- `¬(φ U ψ)` is `¬φ R ¬ψ`
      show (STL.Formula.release (i * c) (j * c) (n₁'.toFormula.scale c)
        (n₂'.toFormula.scale c)).Sat ξ ↔ ¬ (STL.Formula.until (i * c) (j * c) φ ψ).Sat ξ
      rw [STL.Formula.sat_release]
      simp only [STL.Formula.Sat, h₁', h₂']
      push Not
      exact forall₃_congr fun t _ _ => imp_iff_not_or.symm
  | finOpen d φ _ => exact absurd hstl id
  | globOpen d φ _ => exact absurd hstl id


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
