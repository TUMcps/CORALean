import CORALean.ContDynamics.NonlinearSys.NonlinearSys

/-!
# What a `Reach` run of a nonlinear system is taken at

The step width `Δt`, the step count `N` (the horizon is `[0, NΔt]`), the floor
`q` on the Taylor order, which runs at `q + 2` once raised to what every step's
matrix needs, and the maximum zonotope order `o`. `0 < N` because a horizon of
no steps encloses nothing, not even the initial set.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The step width `Δt > 0`, the step count `N > 0`, the Taylor order floor `q`
and the maximum zonotope order `o > 0` a `Reach NonlinearSys.WithSteps` run takes. -/
structure NonlinearSys.ReachParams where
  Δt : ℝ
  hΔt : 0 < Δt
  N : ℕ
  hN : 0 < N
  q : ℕ
  o : ℕ
  ho : 0 < o

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
