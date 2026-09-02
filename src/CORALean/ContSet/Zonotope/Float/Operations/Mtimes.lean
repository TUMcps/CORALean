import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError

/-!
# `Zonotope.mtimes`

The generator count is untouched, the rounding being paid into the box; the old
box travels through the map as a box, by `Interval.mtimes`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}

/-- What `mtimes` owes beyond its nominal part: the centre, and the generators. -/
def Zonotope.mtimesResidual (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) : Interval 𝕋 m :=
  (Interval.residual (mulVecDown M Z.c) (mulVecUp M Z.c) (mulVecDown M Z.c)).plus
    (Zonotope.generatorError (matMulDiff M Z.G))

def Zonotope.mtimes (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 m where
  h := Z.h
  c := mulVecDown M Z.c
  G := matMulDown M Z.G
  E := (Interval.mtimes M Z.E).plus (Zonotope.mtimesResidual M Z)

end CORALean.Float
