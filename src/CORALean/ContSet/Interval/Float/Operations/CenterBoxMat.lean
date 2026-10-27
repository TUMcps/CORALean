module

public import CORALean.ContSet.Interval.Float.Operations.CenterMat

@[expose] public section

/-!
# `Interval.centerBoxMat`, over a floating-point scalar

CORA's `center` of an interval matrix, `(inf + sup) / 2`, as the box the rounded sum leaves it in:
`centerMat` rounds the sum down, the upper end rounds it up, and `half` is exact.

## Inputs
* `I` – interval matrix

## Output
* interval matrix holding the entrywise midpoint
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

/-- The entrywise midpoint between the sum rounded down and rounded up. -/
def Interval.centerBoxMat (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) :=
  ⟨I.centerMat, fun i j => half (addUp (I.inf i j) (I.sup i j))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
