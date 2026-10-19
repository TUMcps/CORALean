module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# A certificate that a matrix is positive definite

For an interval matrix `X` and a proposed factor `L`, the residual `X - L Lᵀ` is bracketed entry by
entry in outward rounding, and the check is that each diagonal entry's lower bound covers the
magnitudes of its row's other entries, rounded up, strictly (`ltStrict`): strict diagonal
dominance, which makes every symmetric residual positive definite, and with it every symmetric
matrix of `X`, `L Lᵀ` being positive semi-definite on sight (`posDef_of_pdCheck`). `psdCheck` is
the same test at `≤`. Symmetry is the caller's to check, as it is a property of the stored floats
and not of the interval.

## Inputs
* `X` – interval matrix
* `L` – factor

## Output
* `true` only if `X - L Lᵀ` is strictly diagonally dominant
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X - L Lᵀ` is certified strictly diagonally dominant. -/
def Ellipsoid.pdCheck (X : Interval (Mat 𝕋 n n)) (L : Mat 𝕋 n n) : Bool :=
  -- the residual's entries, between two roundings
  let lo : Mat 𝕋 n n := fun i j => subDown (X.inf i j) (dotUp (L i) (L j))
  let hi : Mat 𝕋 n n := fun i j => subUp (X.sup i j) (dotDown (L i) (L j))
  (List.finRange n).all fun i =>
    ltStrict (sumUp fun j => if j = i then zero else maximum (hi i j) (neg (lo i j))) (lo i i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
