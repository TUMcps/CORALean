import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.MtimesResidual

/-!
# `ConZonotope.mtimes` over a floating-point scalar

As over ℝ the constraints sit on the coefficients and a linear map never sees them, so `P`
is copied. Centre and generators are rounded, and what that costs goes into the error box
exactly as for `Zonotope.mtimes`: the coefficients of a constrained zonotope lie in
`[-1, 1]`, which is what lets a generator's rounding be a box. The old box travels through
the map by `Interval.mtimes`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.mtimes (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 n) : ConZonotope 𝕋 m where
  h := cZ.h
  c := mulVecDown M cZ.c
  G := matMulDown M cZ.G
  P := cZ.P
  E := (Interval.mtimes M cZ.E).plus (Zonotope.mtimesResidual M cZ.zonotope)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
