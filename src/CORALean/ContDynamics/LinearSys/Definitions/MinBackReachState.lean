import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContSet.ConZonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `Alg. 1`'s loop state

`MinBackReachState`: what one iteration of [1, Alg. 1] hands the next.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 1] hands the next. -/
structure LinearSys.MinBackReachState (n : ℕ) where
  /-- `t_k`, line 8. -/
  t : ℝ
  /-- `Ẑ_{W₀}(-t_k)`, line 9. -/
  ZW₀ : Zonotope (Vec ℝ n)
  /-- `Ẑ_{U₀}(-t_k)`, line 12. -/
  ZU₀ : Zonotope (Vec ℝ n)
  /-- `R̂^∃(-τ_{k-1})`, line 11. -/
  R : ConZonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
