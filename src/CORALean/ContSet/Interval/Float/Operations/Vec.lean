module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.vec`, over a floating-point scalar

CORA's `reshape(·, [], 1)` of an interval matrix: the bounds stacked column by column, entry `(i,
j)` going to position `i + m * j`. Nothing is computed, so nothing rounds.

## Inputs
* `I` – interval matrix

## Output
* interval vector of the stacked bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The column-major stacking of both bounds. -/
def Interval.vec (I : Interval (Mat 𝕋 m n)) : Interval (Vec 𝕋 (n * m)) where
  inf := fun k => I.inf (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  sup := fun k => I.sup (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
