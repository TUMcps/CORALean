module

public import CORALean.Specification.STLInterval.Definitions.Endpoint

@[expose] public section

/-!
# `infimum`

`@stlInterval/infimum.m`: the lower bound (`[]` for the empty interval) and whether it is attained.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.infimum : STLInterval → STLInterval.Endpoint
  | .empty => ⟨none, true⟩
  | .nonempty l _ lc _ _ _ _ _ => ⟨some l, lc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
