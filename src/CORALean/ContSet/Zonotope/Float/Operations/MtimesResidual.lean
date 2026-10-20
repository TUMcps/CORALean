module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Basic

@[expose] public section

/-!
# `Zonotope.mtimesResidual`

What `mtimes` owes beyond its nominal part: the center, rounded, and the
generators, each entry known only to within `matMulDiff`'s rounding gap.

## Inputs
* `M` – matrix
* `Z` – zonotope

## Output
* box of what the product owes beyond its nominal part
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `mtimes` owes beyond its nominal part: the center, and the generators. -/
def Zonotope.mtimesResidual (M : Mat 𝕋 m n) (Z : Zonotope (Vec 𝕋 n)) : Interval (Vec 𝕋 m) :=
  (Interval.residual (mulVecDown M Z.c) (mulVecUp M Z.c) (mulVecDown M Z.c)).plus
    (Zonotope.generatorError (matMulDiff M fun i j => Z.G j i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
