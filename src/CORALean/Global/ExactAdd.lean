import CORALean.Global.ExactScalar

/-!
# A scalar whose `+` is exact

`ExactScalar` has a `0` and a `1` and no `+`, since `toReal (a + b) = toReal a + toReal b` fails
wherever a sum rounds. `ExactAdd` is that law as a class. It holds at `ℝ` and at no float format:
a float sum is rounded, so the class marks exactly where a self-binding at a nonzero `A_ij` can be
assembled (`mergeFlowsAdd`), and where it cannot (#40).
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar


-- ========================================  MAIN TYPE  ========================================= --

class ExactAdd (𝕋 : Type) [Scalar 𝕋] extends Add 𝕋 where
  toReal_add (a b : 𝕋) : toReal (a + b) = toReal a + toReal b

/-- `ℝ` adds exactly. -/
instance : ExactAdd ℝ where
  toReal_add _ _ := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
