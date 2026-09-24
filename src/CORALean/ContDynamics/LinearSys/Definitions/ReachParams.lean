import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# What `Reach LinearSys` needs beyond the initial set

Homogeneous only, as `timeIntervalStep` is: `r` is the whole window `[0, r]`
`reachUnion` is taken over, in one step, `hr` its side condition. The order is
not a field — `reachOrder` derives one admissible for `r` and `sys.A` from
both, which is what lets `reach_outer` ask for nothing further.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The window `[0, r]` (with `0 < r`) a `Reach LinearSys` run is taken over,
in one step. -/
structure LinearSys.ReachParams where
  r : ℝ
  hr : 0 < r

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
