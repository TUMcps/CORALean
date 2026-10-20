module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Float.Operations.Inflate
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# A zonotope as an ellipsoid, over a floating-point scalar

CORA's `ellipsoid(Z)` at full generator count, `fac*(G*G')` with `fac` the generator count `h`:
here the shape `σ² G Gᵀ`, `σ ≥ √h` a proposed scaling, computed as an interval matrix and stored
rounded upward (`inflate`), about the zonotope's center, its error box carried over.

## Inputs
* `Z` – zonotope
* `σ` – scaling factor

## Output
* interval matrix scaled by `σ` squared times generators times their transpose
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps Matrix

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `σ² G Gᵀ`, entrywise between two roundings, `G` the generators as columns. -/
def Zonotope.ellipsoidShape (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) : Interval (Mat 𝕋 n n) :=
  let G : Mat 𝕋 n Z.h := fun i j => Z.G j i
  Interval.smul (mulDown σ σ) (mulUp σ σ) (Interval.matMul (Interval.point G) (Interval.point Gᵀ))

def Zonotope.ellipsoid (Z : Zonotope (Vec 𝕋 n)) (σ : 𝕋) : Ellipsoid 𝕋 n where
  Q := Ellipsoid.inflate (Z.ellipsoidShape σ)
  q := Z.c
  I_error := Z.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
