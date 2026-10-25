module

public import Mathlib.Data.Rat.Defs

@[expose] public section

/-!
# The settings of an adaptive float run

`AdaptiveOptions`: what [1, Alg. 1] takes besides the system and the sets, the
three error budgets `ε_H,max`, `ε_P,max`, `ε_S,max` (exact, in ℚ), the
factor `μ` a step shrinks by, the order `Φ_prop,max`, and the two loop
bounds [1] leaves out: `fuel` for `Alg. 2`'s step sweep, `maxSteps` for
`Alg. 1`'s main loop.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Alg. 1]'s inputs besides the system and the sets, and two loop bounds. -/
structure LinearSys.AdaptiveOptions (𝕋 : Type) where
  /-- `ε_H,max`, the homogeneous solution's widening per step, eq. (21). -/
  εHmax : ℚ
  /-- `ε_P,max`, the particular solution's widening over the horizon, eq. (22). -/
  εPmax : ℚ
  /-- `ε_S,max`, the reduction error over the horizon, eq. (12). -/
  εSmax : ℚ
  /-- `μ ∈ (0, 1)`, `Alg. 2`'s shrinking factor. -/
  μ : 𝕋
  /-- `Φ_prop,max`, the largest truncation order `Alg. 2` tries. -/
  ηmax : ℕ
  /-- How many step sizes `Alg. 2` tries before it gives up. -/
  fuel : ℕ
  /-- How many steps `Alg. 1` takes before it gives up. -/
  maxSteps : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
