import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# What `reach_adaptive` carries

`options.t`, `options.R`, the finite horizon and the admissible errors
`options.error_adm_x_horizon`, `options.error_adm_y_horizon`, from one step of the loop of
[1, Alg. 1] with CORA's tuning to the next.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- What `reach_adaptive` carries: `options.t`, `options.R`, the finite horizon and
`options.error_adm_x_horizon`, `options.error_adm_y_horizon`. -/
structure NonlinDASys.AdaptState (n p : ℕ) where
  t : ℝ
  R : Zonotope (Vec ℝ n)
  h : ℝ
  adm_x : Vec ℝ n
  adm_y : Vec ℝ p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
