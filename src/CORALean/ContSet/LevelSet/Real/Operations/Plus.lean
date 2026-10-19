module

public import CORALean.ContSet.LevelSet.Real.LevelSet

@[expose] public section

/-!
# `LevelSet.plus`

The image of a level set under a translation, a preimage substitution in `f`. CORA's `levelSet`
has no `plus`.

## Inputs
* `L` – level set
* `v` – shift

## Output
* level set whose points `y` have `y - v` in `L`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
