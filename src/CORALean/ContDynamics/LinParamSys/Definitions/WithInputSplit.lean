import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContSet.Interval.Real.Instances

/-!
# A set-valued continuous-time system paired with an input set anywhere

`LinearSys.WithInputSplit` at an interval system matrix, and `LinParamSys.WithInput`
without `0 ∈ U`: [1, Alg. 4]'s split case, the input set taken apart into a
constant `ũ` and a remainder `Ũ` holding the origin before any window is
computed, by `Recentre` on the representation rather than by a field here.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- A `LinParamSys ℐ` paired with the input set every run draws from, wherever
it sits. -/
structure LinParamSys.WithInputSplit (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  sys : LinParamSys ℐ n
  U : S n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
