module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `Interval.symmCora`

CORA's symmetrization of a square matrix, `(X + Xᵀ) / 2`, read on an interval matrix: each end is
the sum of the two mirrored ends, rounded outward, and then halved, which is exact. It contains
every symmetric matrix of `X`. At `nearest` it is the machine's `(x_ij + x_ji) * 0.5`, as CORA
writes it.

## Inputs
* `X` – interval matrix

## Output
* interval matrix holding every symmetric matrix of `X`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       21-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(X + Xᵀ) / 2` of an interval matrix, each end rounded outward before the exact halving. -/
def Interval.symmCora (X : Interval (Mat 𝕋 n n)) : Interval (Mat 𝕋 n n) where
  inf := fun i j => half (addDown (X.inf i j) (X.inf j i))
  sup := fun i j => half (addUp (X.sup i j) (X.sup j i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
