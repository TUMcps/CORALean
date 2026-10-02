import CORALean.ContSet.LevelSet.Real.LevelSet

/-!
# `LevelSet.and_`

CORA's `@levelSet/and_` for two level sets (`aux_and_ls`): the constraints of both, stacked.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `levelSet/and_`: the constraint lists appended, each with its own operators. -/
def LevelSet.and_ (L₁ L₂ : LevelSet n) : LevelSet n where
  m := L₁.m + L₂.m
  f x := Fin.append (L₁.f x) (L₂.f x)
  op := Fin.append L₁.op L₂.op

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
