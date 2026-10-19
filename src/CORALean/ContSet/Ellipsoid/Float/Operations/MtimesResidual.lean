module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Ellipsoid.mtimesResidual`

What `mtimes` owes beyond its nominal part: the center `M q`, stored at its lower rounding. The
shape matrix's rounding is not here, `inflate` having paid it into `Q`.

## Inputs
* `M` – matrix
* `E` – ellipsoid

## Output
* box of what rounding the center `M q` down leaves to pay
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `mtimes` owes beyond its nominal part: the center's rounding. -/
def Ellipsoid.mtimesResidual (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) : Interval (Vec 𝕋 m) :=
  Interval.residual (mulVecDown M E.q) (mulVecUp M E.q) (mulVecDown M E.q)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
