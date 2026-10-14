module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# The fields of an `stlInterval` as CORA stores them

`lower`, `upper`, `leftClosed` and `rightClosed` of a nonempty `@stlInterval` object, where a MATLAB
double may be `NaN`: `upper = none` is `NaN`, which no comparison holds against. `none` as the whole
object is the empty interval (`lower = []`). Used to model what CORA's code builds
(`STLInterval.minkDiffCora`), not as a second type of intervals.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure STLInterval.Fields where
  lower : EReal
  upper : Option EReal
  leftClosed : Bool
  rightClosed : Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
