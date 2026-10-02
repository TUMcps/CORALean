import CORALean.ContSet.LevelSet.Real.Operations.Inf

/-!
# `LevelSet.Inf` denotes the whole space
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.construct_Inf (n : ℕ) : (LevelSet.Inf n).construct = Set.univ := by
  ext x
  simp [LevelSet.Inf, LevelSet.construct, CompOp.holds]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
