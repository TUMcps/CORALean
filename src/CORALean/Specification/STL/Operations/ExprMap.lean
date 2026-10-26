module

public import CORALean.Specification.STL.Definitions.Expr

@[expose] public section

/-!
# Mapping the numbers of an expression

The expression with every number `c` replaced by `g c`; variables, operators and exponents are
kept. At a float scalar `g` reads a number as the real it denotes (`STL.Expr.toReal`).

## Inputs
* `g` – map of the numbers

## Output
* the expression with the numbers mapped
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {κ κ' : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The expression with every number mapped by `g`. -/
def STL.Expr.map (g : κ → κ') : STL.Expr κ n → STL.Expr κ' n
  | .var i => .var i
  | .num c => .num (g c)
  | .add e₁ e₂ => .add (map g e₁) (map g e₂)
  | .sub e₁ e₂ => .sub (map g e₁) (map g e₂)
  | .mul e₁ e₂ => .mul (map g e₁) (map g e₂)
  | .pow e k => .pow (map g e) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
