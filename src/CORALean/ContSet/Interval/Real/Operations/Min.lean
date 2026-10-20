module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.min`

CORA's `@interval/min` at two intervals: `-max(-I, -Y)`, which is the coordinatewise smaller bound
on each side, `[min inf₁ inf₂, min sup₁ sup₂]`. It is written that way here, and
`Theorems/MinEqUminusMax` proves it is `-max(-I, -J)`.

## Inputs
* `I₁` – first interval
* `I₂` – second interval

## Output
* interval of the entrywise minima
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.min (I₁ I₂ : Interval α) : Interval α where
  inf := ofEntry fun i => Min.min (entry I₁.inf i) (entry I₂.inf i)
  sup := ofEntry fun i => Min.min (entry I₁.sup i) (entry I₂.sup i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
