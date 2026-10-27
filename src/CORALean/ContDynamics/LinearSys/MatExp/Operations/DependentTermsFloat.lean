module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.DependentTermsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalWFloat
public import CORALean.ContSet.Interval.Float.Operations.ExactSquare
public import CORALean.ContSet.Interval.Float.Operations.IntervalMatrix
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `MatExp.dependentTerms`, over a floating-point scalar

CORA's `@intervalMatrix/dependentTerms`, rounded outward: the exact square `exactSquare` and the
second-order Taylor term `expIntervalW`, the square scaled by `r²` (bracketed by `mulDown r r` and
`mulUp r r`) and the identity added to the second, each rebuilt from center and radius as CORA
does (`Interval.intervalMatrix`).

## Inputs
* `A` – interval matrix
* `r` – step length

## Output
* squared and linear dependent terms of the interval matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[intSq, intH] = dependentTerms(obj, r)`. -/
def MatExp.dependentTerms (A : Interval (Mat 𝕋 n n)) (r : 𝕋) : MatExp.DependentTerms 𝕋 n where
  intSq := (Interval.smul (mulDown r r) (mulUp r r) (Interval.exactSquare A)).intervalMatrix
  intH := (Interval.matPlus (Interval.point (diagonalBlock fun _ => one))
    (MatExp.expIntervalW A r)).intervalMatrix

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
