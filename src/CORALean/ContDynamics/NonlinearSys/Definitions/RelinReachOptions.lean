import Mathlib.Data.Real.Basic

/-!
# CORA's `options` for the re-linearization loop

`timeStep` and `zonotopeOrder`, CORA's names, as in `LinearSys.ReachOptions`. The
loop takes one step per linearization, so `timeStep` is also the length of each
linearization's horizon; the horizon in `params` counts those steps (see
`NonlinearSys.relinReach`).

`timeStep` is an `ℝ` here, not the `ℚ` of `LinearSys.ReachOptions`: it feeds
`LinearSys.discretize`, which holds `e^{AΔt}` exactly at `ℝ` and has no other
argument. `hZonotopeOrder` rules out `0`, as in `LinearSysDT.ReachOptions`, and
closes at any positive literal by default.

CORA computes each step's linearization and abstraction-error certificate inside
`reach`; here they are the caller's, so they are not in `options` but follow it as
`steps` and `Ud`.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The step `timeStep` and the maximum order `zonotopeOrder` (positive) every
step is reduced to. -/
structure NonlinearSys.RelinReachOptions where
  timeStep : ℝ
  zonotopeOrder : ℕ
  hZonotopeOrder : 0 < zonotopeOrder := by exact Nat.zero_lt_succ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
