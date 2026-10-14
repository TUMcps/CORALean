module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# A bound of an STL interval and whether it belongs

The pair `[infi,isMin] = infimum(obj)` (and `[sup,isMax] = supremum(obj)`) of `@stlInterval`: the
bound, `[]` (`none`) for the empty interval, and its closedness flag.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure STLInterval.Endpoint where
  value : Option EReal
  closed : Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
