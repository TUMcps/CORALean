module

public import CORALean.ContSet.EmptySet.Real.Operations.Interval
public import CORALean.ContSet.Interval.Real.Theorems.EmptyExact
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# `EmptySet.interval` denotes the empty set

For `0 < n`, as `Interval.empty_exact`: in dimension `0` a box with no coordinates contains the
one point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.interval_exact (E : EmptySet n) (hn : 0 < n) :
    E.interval.construct = construct E :=
  Interval.empty_exact hn

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
