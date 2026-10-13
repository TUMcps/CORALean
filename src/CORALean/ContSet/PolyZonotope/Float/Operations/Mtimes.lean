module

public import CORALean.ContSet.Interval.Float.Operations.Mtimes
public import CORALean.ContSet.Interval.Float.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Float.Operations.MtimesResidual

@[expose] public section

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

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.mtimes (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 m) where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := mulVecDown M pZ.c
  G := fun l => mulVecDown M (pZ.G l)
  E := pZ.E
  GI := fun j => mulVecDown M (pZ.GI j)
  err := (Interval.mtimes M pZ.err).plus (PolyZonotope.mtimesResidual M pZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
