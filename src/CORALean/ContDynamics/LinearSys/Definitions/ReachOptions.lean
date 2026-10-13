import Mathlib.Data.Nat.Basic

/-!
# CORA's `options` for a continuous-time linear reach

`Δt`, `η` and `ρ` (CORA's `timeStep`, `taylorTerms`, `zonotopeOrder`), the three
CORA's `config_linearSys_reach` makes mandatory for the constant-step schemes, over the
scalar `𝕋` the run computes in. `η` is a request, as CORA's is not: a
run raises it to the first order its remainder bound admits for `Δt` and
the system matrix, and a theorem asks nothing of it. `ρ` is Girard's
order bound, read only by a scheme that reduces.

`0 < Δt` is no field: a run built from a config at run time could not
prove it, and a float run checks it itself, with the step count, `Reach.steps`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The step width `Δt`, the Taylor order `η` a run starts its
search from, and the order `ρ` a reducing scheme holds its sets at. -/
structure LinearSys.ReachOptions (𝕋 : Type) where
  Δt : 𝕋
  η : ℕ
  ρ : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
