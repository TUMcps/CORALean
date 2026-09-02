import CORALean.ContSet.Ellipsoid.Float.Operations.GeneratorError
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual

/-!
# `Ellipsoid.mtimes`

`G ↦ M G` and `q ↦ M q`, as over ℝ, with both rounded and the difference paid
into the box. The generator count is untouched and the shape stays out of it —
which is the whole reason the generator form is stored: `Q ↦ M Q Mᵀ` would be a
new shape matrix to take a square root of, and here even the *support function's*
square root is only ever checked, never taken.

Exact over ℝ, and only `_outer` here. That gap is the rounding and nothing else.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}

/-- What `mtimes` owes beyond its nominal part: the centre, and the
generators. -/
def Ellipsoid.mtimesResidual (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) : Interval 𝕋 m :=
  (Interval.residual (mulVecDown M E.q) (mulVecUp M E.q) (mulVecDown M E.q)).plus
    (Ellipsoid.generatorError (matMulDiff M E.G))

def Ellipsoid.mtimes (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 m where
  k := E.k
  q := mulVecDown M E.q
  G := matMulDown M E.G
  err := (Interval.mtimes M E.err).plus (Ellipsoid.mtimesResidual M E)

end CORALean.Float
