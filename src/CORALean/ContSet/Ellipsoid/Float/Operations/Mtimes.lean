import CORALean.ContSet.Ellipsoid.Float.Operations.MtimesResidual
import CORALean.ContSet.Interval.Float.Operations.Mtimes

/-!
# `Ellipsoid.mtimes`

`G ↦ M G` and `q ↦ M q`, as over ℝ, with both rounded and the difference paid
into the box. The generator count is untouched and the shape stays out of it —
which is the whole reason the generator form is stored: `Q ↦ M Q Mᵀ` would be a
new shape matrix to take a square root of, and here even the *support function's*
square root is only ever checked, never taken.

Exact over ℝ, and only `_outer` here. That gap is the rounding and nothing else.
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

def Ellipsoid.mtimes (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 m where
  k := E.k
  q := mulVecDown M E.q
  G := matMulDown M E.G
  err := (Interval.mtimes M E.err).plus (Ellipsoid.mtimesResidual M E)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
