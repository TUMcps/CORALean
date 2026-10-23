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

/-- A bound of an STL interval: its value, `none` for the empty interval, and whether the bound
belongs to the interval. -/
structure STLInterval.Endpoint (𝕋 : Type) where
  value : Option (WithTop 𝕋)
  closed : Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
