module

public import CORALean.DiscrDynamics.GridPartition.Definitions.GridPartitionFloat
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `GridPartition.cellInterval`, over a floating-point scalar

The box of one cell: from divider `sub - 1` to divider `sub` in each dimension, the subscripts
coming from the cell number as MATLAB's `ind2sub` does. The stored dividers are copied and nothing
is rounded.

## Inputs
* `P` – grid partition
* `c` – cell number

## Output
* box of the cell
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

/-- The box of cell `c`, from divider `sub - 1` to divider `sub` in each dimension. -/
def GridPartition.cellInterval (P : GridPartition 𝕋 n) (c : ℕ) : Interval (Vec 𝕋 n) where
  inf := fun j => P.dividers j (CORALean.GridPartition.i2s P.nrOfSegments c j - 1)
  sup := fun j => P.dividers j (CORALean.GridPartition.i2s P.nrOfSegments c j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
