module

@[expose] public section

/-!
# CORA's `params` for a system with no input: the initial set and the horizon

`reach(sys, params, options)` in CORA splits a run's arguments in two: `params`
says which problem is solved, `options` how. This is the first half for an
input-free algorithm; `Reach.InputParams` adds `U`, and each algorithm family
declares its own `…ReachOptions` for the second half.

The horizon is CORA's, and the papers': `[tStart, tFinal]`, `tStart` defaulting
to `0` as in CORA. `T` is the time type a family measures in — ℚ for a
continuous run, where the step count `(tFinal - tStart) / Δt` is derived
exactly by `Reach.steps` and a run refuses a horizon it does not divide; ℕ for
`LinearSysDT`, whose time is counted in sampling periods (see its `reach`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The initial set `X₀` and the horizon `[tStart, tFinal]`: CORA's `params.R0`,
`params.tStart` (default `0`) and `params.tFinal`. -/
structure Reach.Params (X T : Type) [Zero T] where
  X₀ : X
  tStart : T := 0
  tFinal : T

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
