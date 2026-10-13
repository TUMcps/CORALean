import Mathlib.Data.Real.Basic

/-!
# CORA's `options` for the re-linearization loop

`Δt` and `ρ` (CORA's `timeStep` and `zonotopeOrder`), as in `LinearSys.ReachOptions`. The
loop takes one step per linearization, so `Δt` is also the length of each
linearization's horizon; the horizon in `params` counts those steps (see
`NonlinearSys.relinReach`).

`Δt` is an `ℝ` here, not the `ℚ` of `LinearSys.ReachOptions`: it feeds
`LinearSys.discretize`, which holds `e^{AΔt}` exactly at `ℝ` and has no other
argument. `hZonotopeOrder` rules out `0`, as in `LinearSysDT.ReachOptions`, and
closes at any positive literal by default.

CORA computes each step's linearization and abstraction-error certificate inside
`reach`; here they are the caller's, so they are not in `options` but follow it as
`steps` and `Ud`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The step `Δt` and the maximum order `ρ` (positive) every
step is reduced to. -/
structure NonlinearSys.RelinReachOptions where
  Δt : ℝ
  ρ : ℕ
  hZonotopeOrder : 0 < ρ := by exact Nat.zero_lt_succ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
