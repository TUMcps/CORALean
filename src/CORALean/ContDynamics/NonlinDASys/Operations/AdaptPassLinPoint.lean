import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptTuning

/-!
# `NonlinDASys.AdaptPass.linPoint`

The linearization of a pass with the errors it settled on: the accepted pass's sets are
`linReach` at it ([1, Alg. 1] with CORA's tuning).

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

open CORALean.Real Matrix ContSet

variable {n p m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The linearization `L` with the abstraction errors the pass settled on: what the accepted
pass's sets are `linReach` at. -/
def NonlinDASys.AdaptPass.linPoint {n p m : ℕ} (pass : NonlinDASys.AdaptPass n p)
    (L : NonlinDASys.LinPoint n p m) : NonlinDASys.LinPoint n p m :=
  { L with Verror := pass.err.Z_error, Verror_y := pass.err.Z_error_y }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
