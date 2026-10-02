import CORALean.ContSet.LevelSet.Real.Operations.And
import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds

/-!
# `LevelSet.and_` is exact

Stacking constraints is intersecting the sets, with equality, whatever the operators.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.and_exact (L₁ L₂ : LevelSet n) :
    (L₁.and_ L₂).construct = L₁.construct ∩ L₂.construct := by
  ext x
  exact LevelSet.forall_append_holds _ _ _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
