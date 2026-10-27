module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.radiusMat`, over a floating-point scalar

CORA's `rad` of an interval matrix, the half-width of each entry: `half` is exact, so only the
difference rounds, and it rounds up.

## Inputs
* `I` – interval matrix

## Output
* matrix of rounded half-widths
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

/-- The half-width of each entry, the difference rounded up. -/
def Interval.radiusMat (I : Interval (Mat 𝕋 m n)) : Mat 𝕋 m n :=
  fun i j => half (subUp (I.sup i j) (I.inf i j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
