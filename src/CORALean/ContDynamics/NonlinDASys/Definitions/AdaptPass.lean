module

public import CORALean.ContDynamics.NonlinDASys.Definitions.AbstractionError

@[expose] public section

/-!
# The step a pass settled on

`linReach_adaptive` halves the step `options.Δt` until the abstraction error loop
converges ([1, Alg. 1] with CORA's tuning); the pass is that step and the errors it
converged to, the outputs the loop that follows needs.

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The step size a pass settled on and the abstraction errors it ran with. -/
structure NonlinDASys.AdaptPass (n p : ℕ) where
  /-- `options.Δt`. -/
  Δt : ℝ
  /-- The abstraction errors the accepted pass converged to. -/
  err : NonlinDASys.AbstractionError n p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
