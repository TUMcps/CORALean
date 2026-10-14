module

public import CORALean.ContSet.LevelSet.Real.LevelSet

@[expose] public section

/-!
# `ContSet/LevelSet/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n : ℕ}


-- =====================================  `LevelSet.empty`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `levelSet.empty(n)`: `1 ≤ 0`, true nowhere.

CORA's `levelSet.empty(n)`: the constant `1 ≤ 0`, true nowhere. -/
def LevelSet.empty (n : ℕ) : LevelSet n := ⟨1, fun _ _ => 1, fun _ => .le⟩


-- ======================================  `LevelSet.Inf`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `levelSet.Inf(n)`: `0 x - 1 ≤ 0`, true everywhere.

CORA's `levelSet.Inf(n)`: the constant `-1 ≤ 0`, true everywhere. -/
def LevelSet.Inf (n : ℕ) : LevelSet n := ⟨1, fun _ _ => -1, fun _ => .le⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
