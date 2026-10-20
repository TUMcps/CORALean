module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi

@[expose] public section

/-!
# `Taylm.boundsProd`

The product of an interval by a list of intervals, factor by factor through the corner products
rounded outward.

## Inputs
* `E` – interval of each factor

## Output
* product of a start interval by the listed factors
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {ι : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.boundsProd (E : ι → Interval 𝕋) : List ι → Interval 𝕋 → Interval 𝕋
  | [], I => I
  | k :: l, I => Taylm.boundsProd E l
    ⟨Interval.mulLo I.inf I.sup (E k).inf (E k).sup, Interval.mulHi I.inf I.sup (E k).inf (E k).sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
