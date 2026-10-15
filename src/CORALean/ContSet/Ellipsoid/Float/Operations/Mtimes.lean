module

public import CORALean.ContSet.Ellipsoid.Float.Operations.MtimesResidual
public import CORALean.ContSet.Ellipsoid.Float.Operations.Inflate
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `Ellipsoid.mtimes`

CORA's `@ellipsoid/mtimes` at a float matrix: `Q ↦ M Q Mᵀ`, `q ↦ M q`. The shape matrix is computed
as an interval matrix (`Interval.matMul` at the stored points) and stored rounded upward,
`inflate`, so its ellipsoid contains the exact one: the shape's rounding goes into `Q`, the
center's into the error box, and the old box travels through `M` as a box.

Exact over ℝ, and only `_outer` here. That gap is the rounding and nothing else.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps Matrix

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.mtimes (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 m :=
  -- `M Q Mᵀ`, entrywise between two roundings
  let MQMt : Interval (Mat 𝕋 m m) :=
    Interval.matMul (Interval.matMul (Interval.point M) (Interval.point E.Q)) (Interval.point Mᵀ)
  { Q := Ellipsoid.inflate MQMt
    q := mulVecDown M E.q
    I_error := (Interval.mtimes M E.I_error).plus (Ellipsoid.mtimesResidual M E) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
