module

public import CORALean.ContSet.Ellipsoid.Float.Operations.GeneratorError
public import CORALean.ContSet.Interval.Float.Operations.Plus
public import CORALean.ContSet.Interval.Float.Operations.Residual

@[expose] public section

/-!
# `Ellipsoid.mtimesResidual`

What `mtimes` owes beyond its nominal part: the centre, rounded, and the
generators, each entry known only to within `matMulDiff`'s rounding gap.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `mtimes` owes beyond its nominal part: the centre, and the
generators. -/
def Ellipsoid.mtimesResidual (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) : Interval (Vec 𝕋 m) :=
  (Interval.residual (mulVecDown M E.q) (mulVecUp M E.q) (mulVecDown M E.q)).plus
    (Ellipsoid.generatorError (matMulDiff M E.G))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
