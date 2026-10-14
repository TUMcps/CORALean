module

public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Definitions.TreeIsCnf

@[expose] public section

/-!
# The clauses of a conjunctive normal form

In a conjunctive normal form, the conjuncts `getClauses(obj,'cnf')` returns are clauses:
disjunctions of leaves.
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

theorem STL.Tree.isClause_of_mem_getClausesCnf (φ : STL.Tree n) (h : φ.IsCnf) (c : STL.Tree n)
    (hc : c ∈ φ.getClausesCnf) : c.IsClause := by -- --- PROOF ---
  induction φ with
  | and φ ψ ihφ ihψ =>
    rcases List.mem_append.1 hc with hc | hc
    · exact ihφ h.1 hc
    · exact ihψ h.2 hc
  | _ => simp_all [STL.Tree.getClausesCnf, STL.Tree.IsCnf]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
