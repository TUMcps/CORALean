module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes
public import CORALean.ContSet.Interval.Float.Operations.SymmCora

@[expose] public section

/-!
# `Ellipsoid.mtimesCora`

CORA.cpp's `@ellipsoid/mtimes` in its own order: the shape matrix is `(M Q) Mᵀ`, then symmetrized
as `(P + Pᵀ) / 2`, and the center is `M q`. Where `Ellipsoid.mtimes` stores the mirrored upper
triangle of `M Q Mᵀ`, this stores the mirrored upper triangle of the symmetrized product, so at
`nearest` every entry is CORA.cpp's bit for bit. The symmetrized interval holds `M Q Mᵀ`, which is
symmetric, so the stored shape is above it as before. Everything else is `Ellipsoid.mtimes`.

## Inputs
* `M` – matrix
* `E` – ellipsoid

## Output
* ellipsoid enclosing `M E`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       21-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps Matrix

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.mtimesCora (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 m :=
  -- `(M Q) Mᵀ`, entrywise between two roundings
  let P : Interval (Mat 𝕋 m m) :=
    Interval.matMul (Interval.matMul (Interval.point M) (Interval.point E.Q)) (Interval.point Mᵀ)
  { Q := Ellipsoid.inflate P.symmCora
    q := mulVecDown M E.q
    I_error := (Interval.mtimes M E.I_error).plus (Ellipsoid.mtimesResidual M E) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
