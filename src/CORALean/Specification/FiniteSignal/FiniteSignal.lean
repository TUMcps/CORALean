module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# Piecewise-constant signals on a finite horizon

CORA's `finiteSignal` (`specification/signals/@finiteSignal`): a signal on `[0, duration]` stored as
strictly increasing `time` and, for each, the `value` held up to it (the last one up to and
including it). CORA's constructor checks the array shape (`IsValid`); here the data is a pair of
lists, over any ordered time type `T` and value type `V`.

## References

None: CORA's `finiteSignal.m` cites no source, and the CORA manual (v2026) does not mention the
class.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A piecewise-constant signal on a finite horizon: strictly increasing times, each with the value
held up to it. -/
structure FiniteSignal (T V : Type) where
  time : List T
  value : List V
  deriving DecidableEq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
