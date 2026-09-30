import Mathlib.Data.Nat.Basic

/-!
# CORA's `options` for a continuous-time linear reach

`timeStep`, `taylorTerms` and `zonotopeOrder`, the three CORA's
`config_linearSys_reach` makes mandatory for the constant-step schemes, over the
scalar `𝕋` the run computes in. `taylorTerms` is a request, as CORA's is not: a
run raises it to the first order its remainder bound admits for `timeStep` and
the system matrix, and a theorem asks nothing of it. `zonotopeOrder` is Girard's
order bound, read only by a scheme that reduces.

`0 < timeStep` is no field: a run built from a config at run time could not
prove it, and a float run checks it itself, with the step count, `Reach.steps`.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The step width `timeStep`, the Taylor order `taylorTerms` a run starts its
search from, and the order `zonotopeOrder` a reducing scheme holds its sets at. -/
structure LinearSys.ReachOptions (𝕋 : Type) where
  timeStep : 𝕋
  taylorTerms : ℕ
  zonotopeOrder : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
