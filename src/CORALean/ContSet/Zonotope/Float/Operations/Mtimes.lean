module

public import CORALean.ContSet.Interval.Float.Operations.Mtimes
public import CORALean.ContSet.Interval.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesResidual

@[expose] public section

/-!
# `Zonotope.mtimes`

The generator count is untouched, the rounding being paid into the box; the old
box travels through the map as a box, by `Interval.mtimes`.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.mtimes (M : Mat 𝕋 m n) (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 m) where
  h := Z.h
  c := mulVecDown M Z.c
  G := fun j => mulVecDown M (Z.G j)
  E := (Interval.mtimes M Z.E).plus (Zonotope.mtimesResidual M Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
