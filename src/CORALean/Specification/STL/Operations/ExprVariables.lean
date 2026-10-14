module

public import CORALean.Specification.STL.Definitions.Expr
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-!
# The variables of an expression

The variables `x(i)` an expression mentions (the `variables` property of CORA's `stl` objects,
which `getVariables` lists). A number has none; `x(i)*0` still mentions `x(i)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The indices of the variables occurring in `e`. -/
def STL.Expr.variables : STL.Expr n → Finset (Fin n)
  | .var i => {i}
  | .num _ => ∅
  | .add e₁ e₂ | .sub e₁ e₂ | .mul e₁ e₂ => e₁.variables ∪ e₂.variables
  | .pow e _ => e.variables

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
