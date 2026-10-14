module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# Piecewise-constant Boolean signals

CORA's `pointSegmentSignal` (`specification/signals/@pointSegmentSignal`): a signal on `[0,∞)`
stored as strictly increasing `timePoints` and, for each, the `values` at the point itself and on
the open interval up to the next point (the last one to infinity). CORA's constructor checks the
array shape (`IsValid`); here the data is a pair of lists, over any ordered time type `T`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure PointSegmentSignal (T : Type) where
  timePoints : List T
  values : List Bool
  deriving DecidableEq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
