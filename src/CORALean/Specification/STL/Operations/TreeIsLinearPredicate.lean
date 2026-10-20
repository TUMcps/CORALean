module

public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Operations.ExprIsLinear

@[expose] public section

/-!
# Linear predicates

`@stl/isLinearPredicate.m`: a conjunction of comparisons of linear expressions. A formula with a
temporal operator is not one, and neither is `true`, `false`, `~` or `|`. CORA tests
`obj.temporal`
first; the clauses below reject a temporal operator as well, so the test is not repeated.

## Inputs
* none

## Output
* whether the formula is a conjunction of linear comparisons
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

/-- `isLinearPredicate(obj)`. -/
def STL.Tree.isLinearPredicate : STL.Tree n → Bool
  | .cmp _ e₁ e₂ => e₁.isLinear && e₂.isLinear
  | .and φ ψ => φ.isLinearPredicate && ψ.isLinearPredicate
  | _ => false

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
