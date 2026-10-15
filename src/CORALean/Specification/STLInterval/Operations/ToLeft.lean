module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `toLeft`: the interval to the left

`@stlInterval/toLeft.m`: `[0, lower)`, or `[0, lower]` when the lower end is open. `none` is CORA's
`CORA:emptySet` error on the empty interval.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.toLeft : STLInterval → Option STLInterval
  | .empty => none
  | .nonempty l _ lc _ _ _ _ _ => some (stlInterval 0 l true (!lc) le_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
