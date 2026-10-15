module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# A set reachable in a time interval

One element `R.timeInterval.set{i}` of a reach set together with its time interval
`R.timeInterval.time{i}` = `interval(lo,hi)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure ReachSetAnalyzer.TimedSet (S : ℕ → Type) (n : ℕ) where
  set : S n
  /-- The time interval `interval(lo,hi)`, read through `inf` and `sup`. -/
  time : Real.Interval ℝ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
