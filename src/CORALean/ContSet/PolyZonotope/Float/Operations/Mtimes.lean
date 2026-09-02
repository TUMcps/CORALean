import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# `PolyZonotope.mtimes`

The exact layer's `map` at `A *ᵥ ·`, which is the only shape a float layer can
take it in: a map given as a matrix rather than as a `LinearMap`, so `map` has
no float counterpart and `mtimes` is the operation.

All three counts are untouched and the exponent matrix is copied, the rounding
being paid into the box; the old box travels through the map as a box, by
`Interval.mtimes`. The two generator blocks round separately and pay into the
same kind of box for the same reason — a monomial is bounded by `1` exactly as
an independent coefficient is.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}

/-- What `mtimes` owes beyond its nominal part: the centre, and both generator
blocks. -/
def PolyZonotope.mtimesResidual (M : Mat 𝕋 m n) (PZ : PolyZonotope 𝕋 n) : Interval 𝕋 m :=
  ((Interval.residual (mulVecDown M PZ.c) (mulVecUp M PZ.c) (mulVecDown M PZ.c)).plus
      (PolyZonotope.generatorError (matMulDiff M PZ.G))).plus
    (PolyZonotope.generatorError (matMulDiff M PZ.GI))

def PolyZonotope.mtimes (M : Mat 𝕋 m n) (PZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 m where
  p := PZ.p
  h := PZ.h
  q := PZ.q
  c := mulVecDown M PZ.c
  G := matMulDown M PZ.G
  E := PZ.E
  GI := matMulDown M PZ.GI
  err := (Interval.mtimes M PZ.err).plus (PolyZonotope.mtimesResidual M PZ)

end CORALean.Float
