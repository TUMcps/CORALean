module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# A clause of a conjunctive normal form

A formula with no `&` above a leaf: a leaf (a comparison, `true`, `false`, `~`, a temporal
operator) or an `|` of clauses. The literals of `getClauses` for a CNF.

## Inputs
* none

## Output
* the formula is a disjunction of leaves
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `φ` is a disjunction of leaves. -/
def STL.Tree.IsClause : STL.Tree n → Prop
  | .and _ _ => False
  | .or φ ψ => IsClause φ ∧ IsClause ψ
  | _ => True

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
