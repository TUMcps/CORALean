import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContSet.Interval.Real.Instances

/-!
# A set-valued continuous-time system paired with its input set

`LinearSys.WithInput` at an interval system matrix: `Reach.Params` is not
indexed by `n`, so the input set `U` is bundled with the system, and `0 ∈ U` is
a field, being what buys one enclosure for the whole step
(`ConstTrajectory.inputSolution_timeInterval_outer`). An input set off the
origin is the split case, a constant taken off first, which `reachUnion` does
not do.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- A `LinParamSys ℐ` paired with the input set every run draws from, which
holds the origin. -/
structure LinParamSys.WithInput (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  sys : LinParamSys ℐ n
  U : S n
  zero_mem_U : (0 : Vec ℝ n) ∈ construct U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
