module

public import CORALean.ContSet.LevelSet.Real.LevelSet

@[expose] public section

/-!
# `LevelSet.empty`

CORA's `levelSet.empty(n)`: the constant `1 ≤ 0`, true nowhere.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `levelSet.empty(n)`: `1 ≤ 0`, true nowhere. -/
def LevelSet.empty (n : ℕ) : LevelSet n := ⟨1, fun _ _ => 1, fun _ => .le⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
