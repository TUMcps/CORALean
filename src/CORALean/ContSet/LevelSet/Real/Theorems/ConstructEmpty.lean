import CORALean.ContSet.LevelSet.Real.Operations.Empty
import CORALean.ContSet.LevelSet.Real.Theorems.MemConstruct

/-!
# `LevelSet.empty` denotes the empty set
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.construct_empty (n : ℕ) : (LevelSet.empty n).construct = ∅ := by
  ext x
  simp [LevelSet.empty, LevelSet.construct, CompOp.holds]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
