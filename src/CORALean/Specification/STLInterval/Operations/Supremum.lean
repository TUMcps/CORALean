module

public import CORALean.Specification.STLInterval.Definitions.Endpoint
public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `supremum`

`@stlInterval/supremum.m`: the upper bound (`[]` for the empty interval) and whether it is attained.

## Inputs
* none

## Output
* the supremum of the interval with its closedness
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.supremum : STLInterval 𝕋 → STLInterval.Endpoint 𝕋
  | .empty => ⟨none, true⟩
  | .nonempty _ u _ rc _ _ _ => ⟨some u, rc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
