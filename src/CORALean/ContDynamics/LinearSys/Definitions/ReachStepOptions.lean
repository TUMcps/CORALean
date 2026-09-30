import Mathlib.Data.Nat.Basic

/-!
# CORA's `options` for a continuous-time linear reach that does not reduce

`timeStep` and `taylorTerms`, the two of `LinearSys.ReachOptions` that a scheme without order
reduction reads: the real-valued `reach`, `reachWrappingFree`, `WithInput.reach` and
`WithInputSplit.reach` keep every set at the order the recursion gives it, so
`zonotopeOrder` would be a field nobody reads. Over the scalar `𝕋` the run computes in,
here `ℝ`, the field the reach's theorems are stated in.

`taylorTerms` is a request, as CORA's is not: a run raises it to the first order its
remainder bound admits for `timeStep` and the system matrix, and a theorem asks nothing of
it. `0 < timeStep` is no field, a theorem asks it.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The step width `timeStep` and the Taylor order `taylorTerms` a run starts its search from. -/
structure LinearSys.ReachStepOptions (𝕋 : Type) where
  timeStep : 𝕋
  taylorTerms : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
