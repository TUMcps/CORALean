module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `toLeft`: the interval to the left

`@stlInterval/toLeft.m`: `[0, lower)`, or `[0, lower]` when the lower end is open. `none` is CORA's
`CORA:emptySet` error on the empty interval.

## Inputs
* none

## Output
* the interval to the left, or none if empty
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.toLeft : STLInterval 𝕋 → Option (STLInterval 𝕋)
  | .empty => none
  | .nonempty l _ lc _ _ _ _ => some (stlInterval 0 (l : WithTop 𝕋) true (!lc) toReal_zero_eq.ge)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
