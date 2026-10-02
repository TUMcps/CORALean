import CORALean.ContSet.LevelSet.Real.LevelSet

/-!
# `LevelSet.lift_`

CORA's `@levelSet/lift_`: the equation on the old variables, substituted by the new variables
`x(dims)`. The new coordinates are unconstrained.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `levelSet/lift_(ls, N, dims)`: `dims i` is the new coordinate of old variable `i`. -/
def LevelSet.lift_ (L : LevelSet n) (dims : Fin n → Fin N) : LevelSet N where
  m := L.m
  f x := L.f fun i => x (dims i)
  op := L.op

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
