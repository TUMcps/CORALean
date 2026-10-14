module

public import CORALean.Specification.STL.Operations.TreeConjunctiveNormalForm
public import CORALean.Specification.STL.Theorems.TreeSatCnfLoop
public import CORALean.Specification.STL.Theorems.Basic

@[expose] public section

/-!
# The conjunctive normal form keeps the meaning

`conjunctiveNormalForm(obj)` is satisfied by the same traces as `obj` (`Tree.Sat`, CORA's reading
of `until`), with or without the negation normal form step.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_conjunctiveNormalForm (φ : STL.Tree n) (nnf : Bool) (ξ : ℝ≥0 → Fin n → ℝ) :
    (φ.conjunctiveNormalForm nnf).Sat ξ ↔ φ.Sat ξ := by -- --- PROOF ---
  unfold STL.Tree.conjunctiveNormalForm
  rw [STL.Tree.sat_cnfLoop]
  cases nnf
  · exact STL.Tree.sat_negationNormalForm φ ξ
  · exact Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
