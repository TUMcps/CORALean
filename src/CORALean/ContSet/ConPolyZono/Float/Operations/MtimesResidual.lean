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

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}

/-- What `mtimes` owes beyond its nominal part: the centre, and both generator
blocks. The constraints owe nothing, being copied. -/
def ConPolyZono.mtimesResidual (M : Mat 𝕋 k n) (C : ConPolyZono 𝕋 n) : Interval 𝕋 k :=
  ((Interval.residual (mulVecDown M C.c) (mulVecUp M C.c) (mulVecDown M C.c)).plus
      (PolyZonotope.generatorError (matMulDiff M C.G))).plus
    (PolyZonotope.generatorError (matMulDiff M C.GI))

end CORALean.Float
