import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `Alg. 1`'s loop state

`TunedState`: what one iteration of [1, Alg. 1] hands the next.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 1] hands the next. -/
structure LinearSys.TunedState (n : ℕ) where
  /-- `t_i`, line 10. -/
  t : ℝ
  /-- `Δt_{i-1}`, the step `Alg. 2` enlarges at its own line 1. -/
  Δt : ℝ
  /-- `Φ_prop,i`, the truncation order `Alg. 2` settled on. -/
  η : ℕ
  /-- `ε_P([0,t_i])`, eq. (9). -/
  εP : ℝ
  /-- `ε_S([0,t_i])`, eq. (12). -/
  εS : ℝ
  /-- `PR([0,t_i])`, eq. (2), as `Alg. 3` last reduced it. -/
  PR : Zonotope (Vec ℝ n)
  /-- `R([t_{i-1},t_i])`, line 9. -/
  R : Zonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
