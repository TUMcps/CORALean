import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# What `ConPolyZono.mtimes` owes beyond its nominal part

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

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `mtimes` owes beyond its nominal part: the centre, and both generator
blocks. The constraints owe nothing, being copied. -/
def ConPolyZono.mtimesResidual (M : Mat 𝕋 k n) (cPZ : ConPolyZono 𝕋 n) : Interval (Vec 𝕋 k) :=
  ((Interval.residual (mulVecDown M cPZ.c) (mulVecUp M cPZ.c) (mulVecDown M cPZ.c)).plus
      (PolyZonotope.generatorError (matMulDiff M fun i l => cPZ.G l i))).plus
    (PolyZonotope.generatorError (matMulDiff M fun i j => cPZ.GI j i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
