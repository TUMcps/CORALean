module

public import CORALean.Specification.STL.Operations.TreeConjunctiveNormalForm
public import CORALean.Specification.STL.Operations.TreeCnfLoop
public import CORALean.Specification.STL.Operations.TreeCnfRewrite
public import CORALean.Specification.STL.Theorems.Basic

@[expose] public section

/-!
# The conjunctive normal form keeps the meaning

`conjunctiveNormalForm(obj)` is satisfied by the same traces as `obj` (`Tree.Sat`, CORA's reading
of `until`), with or without the negation normal form step.

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

/-- One CNF pass keeps the meaning. -/
theorem STL.Tree.aux_sat_cnfRewrite (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (φ.cnfRewrite).1.Sat ξ ↔ φ.Sat ξ := by -- --- PROOF ---
  induction φ generalizing ξ with
  | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.cnfRewrite]
    split <;> (have e₁ := ihφ ξ; have e₂ := ihψ ξ; simp_all only [STL.Tree.Sat] <;> grind)
  | and φ ψ ihφ ihψ => simp [STL.Tree.cnfRewrite, STL.Tree.Sat, ihφ, ihψ]
  | _ => simp [STL.Tree.cnfRewrite]


/-- The CNF loop keeps the meaning. -/
theorem STL.Tree.aux_sat_cnfLoop (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    φ.cnfLoop.Sat ξ ↔ φ.Sat ξ := by
  induction φ using STL.Tree.cnfLoop.induct generalizing ξ with
  | case1 φ cnt hc => rw [STL.Tree.cnfLoop, dif_pos hc]; exact STL.Tree.aux_sat_cnfRewrite φ ξ
  | case2 φ res cnt h ih =>
    rw [STL.Tree.cnfLoop, dif_neg h, ih, STL.Tree.aux_sat_cnfRewrite]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_conjunctiveNormalForm (φ : STL.Tree n) (nnf : Bool)
    (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (φ.conjunctiveNormalForm nnf).Sat ξ ↔ φ.Sat ξ := by -- --- PROOF ---
  unfold STL.Tree.conjunctiveNormalForm
  rw [STL.Tree.aux_sat_cnfLoop]
  cases nnf
  · exact STL.Tree.sat_negationNormalForm φ ξ
  · exact Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
