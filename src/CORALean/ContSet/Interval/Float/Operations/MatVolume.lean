module

public import CORALean.ContSet.Interval.Float.Operations.Vec
public import CORALean.ContSet.Interval.Float.Operations.Volume

@[expose] public section

/-!
# `Interval.matVolume`, over a floating-point scalar

CORA's `volume` of an interval matrix, which is `volume` of the interval of its entries: the
product of the entry widths, each rounded up and clipped at zero, the product rounded up.

## Inputs
* `I` – interval matrix

## Output
* upper bound of the volume of the box
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

/-- The upper bound of the volume of the stacked box. -/
def Interval.matVolume (I : Interval (Mat 𝕋 m n)) : 𝕋 := I.vec.volume

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
