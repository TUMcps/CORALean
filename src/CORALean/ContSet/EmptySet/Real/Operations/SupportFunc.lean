import CORALean.ContSet.EmptySet.Real.EmptySet
import Mathlib.Data.EReal.Basic

/-!
# `EmptySet.supportFunc`

CORA's `@emptySet/supportFunc_` for type `'upper'`: `-Inf`, the supremum over no point. It is a
value of `EReal`, not `ℝ`, since no real number is the supremum of nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/supportFunc_`, `'upper'`: `-Inf`. -/
noncomputable def EmptySet.supportFunc (_ : EmptySet n) (_ : Vec ℝ n →ₗ[ℝ] ℝ) : EReal := ⊥

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
