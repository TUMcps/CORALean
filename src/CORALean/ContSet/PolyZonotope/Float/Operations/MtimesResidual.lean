import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# What `mtimes` owes beyond its nominal part

Split out of `Mtimes.lean` (issue #62): read again by
`Theorems/MtimesOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `mtimes` owes beyond its nominal part: the centre, and both generator
blocks. -/
def PolyZonotope.mtimesResidual (M : Mat 𝕋 m n) (pZ : PolyZonotope 𝕋 n) : Interval 𝕋 m :=
  ((Interval.residual (mulVecDown M pZ.c) (mulVecUp M pZ.c) (mulVecDown M pZ.c)).plus
      (PolyZonotope.generatorError (matMulDiff M pZ.G))).plus
    (PolyZonotope.generatorError (matMulDiff M pZ.GI))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
