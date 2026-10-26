module

public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Operations.ExprVariables

@[expose] public section

/-!
# The variables of a formula

`@stl/getVariables.m`: the variables a formula mentions. CORA returns their names, sorted by
length and then alphabetically; the variables here are the indices `i` of `x(i)`, so the result is
the set of indices, whose order is not modelled.

## Inputs
* none

## Output
* the variables occurring in the formula
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {τ κ : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `getVariables(obj)`. -/
def STL.Tree.getVariables : STL.Tree τ κ n → Finset (Fin n)
  | .tt | .ff => ∅
  | .cmp _ e₁ e₂ => e₁.variables ∪ e₂.variables
  | .not φ | .next _ φ | .finally _ _ φ | .globally _ _ φ => getVariables φ
  | .and φ ψ | .or φ ψ | .until _ _ φ ψ | .release _ _ φ ψ => getVariables φ ∪ getVariables ψ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
