module

public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# The disjuncts of a formula

The clauses `getClauses(obj,'dnf')` returns, the disjuncts of the formula, are satisfied by a
trace exactly when one of them is.
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

theorem STL.Tree.sat_getClausesDnf (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    φ.Sat ξ ↔ ∃ c ∈ φ.getClausesDnf, c.Sat ξ := by
  induction φ with
  | or φ ψ ihφ ihψ =>
    simp [STL.Tree.getClausesDnf, STL.Tree.Sat, ihφ, ihψ, or_and_right, exists_or]
  | _ => simp [STL.Tree.getClausesDnf]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
