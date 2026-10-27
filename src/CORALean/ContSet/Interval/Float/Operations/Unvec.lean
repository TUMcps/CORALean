module

public import CORALean.ContSet.Interval.Float.Operations.Vec

@[expose] public section

/-!
# `Interval.unvec`, over a floating-point scalar

The inverse of `Interval.vec`, CORA's `reshape(·, n, m)` of a stacked interval back into an
interval matrix. Entries are moved, not computed, so nothing rounds.

## Inputs
* `I` – interval vector of stacked bounds

## Output
* interval matrix of the unstacked bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Entry `(i, j)` is position `i + m * j` of each bound. -/
def Interval.unvec (I : Interval (Vec 𝕋 (n * m))) : Interval (Mat 𝕋 m n) where
  inf := fun i j => I.inf (finProdFinEquiv (j, i))
  sup := fun i j => I.sup (finProdFinEquiv (j, i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
