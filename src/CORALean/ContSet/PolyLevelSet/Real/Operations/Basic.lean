module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.And

@[expose] public section

/-!
# `ContSet/PolyLevelSet/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ==================================  `PolyLevelSet.andRows`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `and_`'s rows on the first operand's box: further rows on the same variables, as an operation
that adds rows to a constraint (an intersection's agreement rows, a union's selector rows) uses. -/
def PolyLevelSet.andRows (P Q : PolyLevelSet n) : PolyLevelSet n := { P.and_ Q with dom := P.dom }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
