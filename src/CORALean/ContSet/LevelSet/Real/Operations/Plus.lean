import CORALean.ContSet.LevelSet.Real.LevelSet

/-!
# `LevelSet.plus`

The image of a level set under a translation, a preimage substitution in `f`. CORA's `levelSet`
has no `plus`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L + v`: `y` is in it when `y - v` is in `L`. -/
def LevelSet.plus (L : LevelSet n) (v : Vec ℝ n) : LevelSet n where
  m := L.m
  f y := L.f (y - v)
  op := L.op

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
