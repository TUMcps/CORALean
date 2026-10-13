module

public import CORALean.ContSet.LevelSet.Real.Operations.Inf

@[expose] public section

/-!
# `LevelSet.Inf` denotes the whole space
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.construct_Inf (n : ℕ) : (LevelSet.Inf n).construct = Set.univ := by
  ext x
  simp [LevelSet.Inf, LevelSet.construct, CompOp.holds]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
