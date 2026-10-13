module

public import CORALean.ContDynamics.LinProbSys.LinProbSys
public import CORALean.ContSet.ProbZonotope.Real.ProbZonotope
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# What `post` carries from one step to the next

The four sets `linProbSys/post` reads from `options` and writes back [1]: the homogeneous
solution `Rhom`, the deterministic particular solution as a box `Rpar_det` and the zonotope
`RauxDet` it grows by, and the probabilistic particular solution `Rpar_prob`.

## References

* [1] `contDynamics/@linProbSys/post.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure LinProbSys.PostState (n : ℕ) where
  Rhom : Zonotope (Vec ℝ n)
  Rpar_det : Interval (Vec ℝ n)
  Rpar_prob : ProbZonotope n
  RauxDet : Zonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
