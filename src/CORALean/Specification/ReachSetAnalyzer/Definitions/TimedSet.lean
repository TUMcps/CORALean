module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# A set reachable in a time interval

One element `R.timeInterval.set{i}` of a reach set together with its time interval
`R.timeInterval.time{i}` = `interval(lo,hi)`, its bounds time stamps of the time type `T`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A reachable set together with the time interval it is reachable in. -/
structure ReachSetAnalyzer.TimedSet (T : Type) (S : ℕ → Type) (n : ℕ) where
  set : S n
  /-- The time interval `interval(lo,hi)`, read through `inf` and `sup`. -/
  time : Real.Interval T

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
