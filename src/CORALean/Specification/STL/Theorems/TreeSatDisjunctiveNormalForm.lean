module

public import CORALean.Specification.STL.Operations.TreeDisjunctiveNormalForm
public import CORALean.Specification.STL.Operations.TreeDnfLoop
public import CORALean.Specification.STL.Operations.TreeDnfRewrite
public import CORALean.Specification.STL.Theorems.Basic

@[expose] public section

/-!
# The disjunctive normal form keeps the meaning

`disjunctiveNormalForm(obj)` is satisfied by the same traces as `obj` (`Tree.Satisfies`, CORA's
reading of `until`), with or without the negation normal form step.

## Inputs
* `φ` – formula
* `nnf` – formula is in negation normal form
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the normal form keeps the meaning
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One DNF pass keeps the meaning. -/
theorem STL.Tree.aux_sat_dnfRewrite (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (φ.dnfRewrite).1.Satisfies ξ ↔ φ.Satisfies ξ := by -- --- PROOF ---
  induction φ generalizing ξ with
  | and φ ψ ihφ ihψ =>
    simp only [STL.Tree.dnfRewrite]
    split <;> (have e₁ := ihφ ξ; have e₂ := ihψ ξ; simp_all only [STL.Tree.Satisfies] <;> grind)
  | or φ ψ ihφ ihψ => simp [STL.Tree.dnfRewrite, STL.Tree.Satisfies, ihφ, ihψ]
  | _ => simp [STL.Tree.dnfRewrite]


/-- The DNF loop keeps the meaning. -/
theorem STL.Tree.aux_sat_dnfLoop (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    φ.dnfLoop.Satisfies ξ ↔ φ.Satisfies ξ := by
  induction φ using STL.Tree.dnfLoop.induct generalizing ξ with
  | case1 φ cnt hc => rw [STL.Tree.dnfLoop, dif_pos hc]; exact STL.Tree.aux_sat_dnfRewrite φ ξ
  | case2 φ res cnt h ih =>
    rw [STL.Tree.dnfLoop, dif_neg h, ih, STL.Tree.aux_sat_dnfRewrite]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_disjunctiveNormalForm (φ : STL.Tree n) (nnf : Bool)
    (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (φ.disjunctiveNormalForm nnf).Satisfies ξ ↔ φ.Satisfies ξ := by -- --- PROOF ---
  unfold STL.Tree.disjunctiveNormalForm
  rw [STL.Tree.aux_sat_dnfLoop]
  cases nnf
  · exact STL.Tree.sat_negationNormalForm φ ξ
  · exact Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
