module

public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Definitions.TreeIsDnf

@[expose] public section

/-!
# The cubes of a disjunctive normal form

In a disjunctive normal form, the disjuncts `getClauses(obj,'dnf')` returns are cubes:
conjunctions of leaves.

## Inputs
* `φ` – formula
* `c` – subformula

## Hypotheses
* `h` – the formula is in disjunctive normal form
* `hc` – the subformula is one of its cubes

## Conclusion
* the subformula is a cube
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

theorem STL.Tree.isCube_of_mem_getClausesDnf (φ : STL.Tree NNReal ℝ n) (h : φ.IsDnf) (c :
  STL.Tree NNReal ℝ n)
    (hc : c ∈ φ.getClausesDnf) : -- --- CONCL ---
    c.IsCube := by -- --- PROOF ---
  induction φ with
  | or φ ψ ihφ ihψ =>
    rcases List.mem_append.1 hc with hc | hc
    · exact ihφ h.1 hc
    · exact ihψ h.2 hc
  | _ => simp_all [STL.Tree.getClausesDnf, STL.Tree.IsDnf]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
