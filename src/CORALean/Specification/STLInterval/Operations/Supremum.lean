module

public import CORALean.Specification.STLInterval.Definitions.Endpoint

@[expose] public section

/-!
# `supremum`

`@stlInterval/supremum.m`: the upper bound (`[]` for the empty interval) and whether it is attained.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.supremum : STLInterval → STLInterval.Endpoint
  | .empty => ⟨none, true⟩
  | .nonempty _ u _ rc _ _ _ _ => ⟨some u, rc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
