module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# Piecewise-constant Boolean signals

CORA's `pointSegmentSignal` (`specification/signals/@pointSegmentSignal`): a signal on `[0,∞)`
stored as strictly increasing `timePoints` and, for each, the `values` at the point itself and on
the open interval up to the next point (the last one to infinity). CORA's constructor checks the
array shape (`IsValid`); here the data is a pair of lists, over any ordered time type `T`.

A signal stored this way has finitely many changes, the finite variability that
[1, Sec. 2.3 (signals)] needs for the unitary decomposition of a Boolean signal.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A piecewise-constant Boolean signal on `[0, ∞)`: strictly increasing time points, each with the
value at the point and on the open interval up to the next. -/
structure PointSegmentSignal (T : Type) where
  timePoints : List T
  values : List Bool
  deriving DecidableEq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
