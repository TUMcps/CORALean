module

public import CORALean.Specification.STL.Definitions.Expr

@[expose] public section

/-!
# Linear expressions

`@stl/isLinearPredicate.m`, `aux_recursive`: a variable or number, a sum or difference of linear
expressions, or a product of a number and a linear expression. A power is not linear (not even
`x^1`), and a product of two non-numeric operands is not.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The expression passes `isLinearPredicate`'s `aux_recursive`. -/
def STL.Expr.isLinear : STL.Expr n → Bool
  | .var _ | .num _ => true
  | .add e₁ e₂ | .sub e₁ e₂ => e₁.isLinear && e₂.isLinear
  | .mul (.num _) e | .mul e (.num _) => e.isLinear
  | _ => false

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
