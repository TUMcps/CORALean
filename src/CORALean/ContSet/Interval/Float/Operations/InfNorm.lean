module

public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat

@[expose] public section

/-!
# `Interval.infNorm`, over a floating-point scalar

CORA's `infNorm`, the maximum row sum of `abs(intMat)`: the entrywise larger end in absolute
value, the row sums rounded up, the maximum exact.

## Inputs
* `I` – interval matrix

## Output
* upper bound of the largest norm of a member in the maximum row sum
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

/-- The largest row sum of `magnitudeMat`, the sums rounded up. -/
def Interval.infNorm (I : Interval (Mat 𝕋 m n)) : 𝕋 :=
  maximumOver fun i => sumUp fun j => I.magnitudeMat i j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
