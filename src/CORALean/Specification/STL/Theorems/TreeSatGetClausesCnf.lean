module

public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# The conjuncts of a formula

The clauses `getClauses(obj,'cnf')` returns, the conjuncts of the formula, are satisfied together
exactly when the formula is.

## Inputs
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the formula holds iff every conjunct holds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_getClausesCnf (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    φ.Satisfies ξ ↔ ∀ c ∈ φ.getClausesCnf, c.Satisfies ξ := by
  induction φ with
  | and φ ψ ihφ ihψ =>
    simp [STL.Tree.getClausesCnf, STL.Tree.Satisfies, ihφ, ihψ, or_imp, forall_and]
  | _ => simp [STL.Tree.getClausesCnf]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
