import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorTail
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalW
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Operations.Smul

/-!
# Interval matrices: the Taylor truncation with an exact second order

`expIntervalTaylorExact`: the truncation of [1, Thm. 3.2]: the identity and `W(t)` exactly,
the rest by interval arithmetic.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The truncation of [1, Thm. 3.2]: the identity and `W(t)` exactly, the rest
by interval arithmetic. -/
noncomputable def MatExp.expIntervalTaylorExact (A : Interval (Mat ℝ n n)) (t : ℝ)
    (κ : ℕ) : Interval (Mat ℝ n n) :=
  Interval.plus (Interval.plus (Interval.point 1) (MatExp.expIntervalW A t))
    (MatExp.expIntervalTaylorTail (Interval.smul t A) κ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
