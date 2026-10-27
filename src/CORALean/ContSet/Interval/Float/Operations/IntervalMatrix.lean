module

public import CORALean.ContSet.Interval.Float.Operations.CenterBoxMat
public import CORALean.ContSet.Interval.Float.Operations.RadiusMat

@[expose] public section

/-!
# `Interval.intervalMatrix`, over a floating-point scalar

CORA's rebuilding of an interval matrix from its center and radius, `intervalMatrix(C, D)` with `C
= ½ (min + max)` and `D = ½ (max - min)`. The center is bracketed by `centerBoxMat` and the
half-width rounds up, so the lower bound is the lower end of the center minus the radius, rounded
down, and the upper bound is the upper end plus the radius, rounded up.

## Inputs
* `I` – interval matrix of the minimum and maximum

## Output
* interval matrix rebuilt from center and radius, rounded outward
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The center minus the radius, rounded down, to the center plus the radius, rounded up. -/
def Interval.intervalMatrix (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) where
  inf := fun i j => subDown (I.centerBoxMat.inf i j) (I.radiusMat i j)
  sup := fun i j => addUp (I.centerBoxMat.sup i j) (I.radiusMat i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
