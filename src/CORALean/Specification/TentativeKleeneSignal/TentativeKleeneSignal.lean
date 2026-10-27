module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal

@[expose] public section

/-!
# Tentative Kleene signals

CORA's `tentativeKleeneSignal` (`specification/signals/tentativeKleeneSignal.m`): what an
observation of a signal leaves possible, stored as two Boolean `pointSegmentSignal`s, `canBeTrue`
and `canBeFalse`. A time where only the first holds is `True`, only the second `False`, both
`Unknown`, neither `Inconclusive` (nothing observed there yet), the values of
[1, Sec. 2.2 (values)]. The constructor checks nothing; `TentativeKleeneSignal.at` is the value they
denote.

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- What an observation of a signal leaves possible: a Boolean signal of the times it can be true
and one of the times it can be false. -/
structure TentativeKleeneSignal (T : Type) where
  canBeTrue : PointSegmentSignal T
  canBeFalse : PointSegmentSignal T
  deriving DecidableEq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
