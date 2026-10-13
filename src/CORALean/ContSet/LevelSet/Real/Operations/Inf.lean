import CORALean.ContSet.LevelSet.Real.LevelSet

/-!
# `LevelSet.Inf`

CORA's `levelSet.Inf(n)`: the constant `-1 ≤ 0`, true everywhere.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `levelSet.Inf(n)`: `0 x - 1 ≤ 0`, true everywhere. -/
def LevelSet.Inf (n : ℕ) : LevelSet n := ⟨1, fun _ _ => -1, fun _ => .le⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
