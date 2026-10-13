import CORALean.ContDynamics.NonlinDASys.Operations.LinReach
import CORALean.ContDynamics.NonlinDASys.Definitions.LinPoint

/-!
# `NonlinDASys.linReachAt`

The sets of one DAE linearization step at the linearization `L`, [1, Alg. 1] line 18: the
fixed-step `NonlinDASys.linReach` at `L`'s Jacobians, point and errors (CORA's tuning).

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

/-- The sets of one DAE linearization step: `linReach` at the linearization `L`. -/
noncomputable def NonlinDASys.linReachAt (sys : NonlinDASys n p m) (L : NonlinDASys.LinPoint n p m)
    (Rinit : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (Δt : ℝ) (η : ℕ) :
    Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n × Vec ℝ p) :=
  NonlinDASys.linReach (sys.f L.xs L.ys L.us) (sys.g L.xs L.ys L.us) L.A L.B L.C L.D L.E
    L.F_inv L.xs L.ys L.us Rinit U L.Verror L.Verror_y Δt η

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
