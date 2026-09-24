import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import CORALean.ContSet.Interval.Real.Operations.AbsMax

/-!
# Interval matrices: enclosing the exponential of an interval matrix

`expIntervalEnclosure`: [1, Sec. 3.3.1]: `expTaylor`/`expEnclosure` at one matrix, widened to
bound every matrix a whole box could hold. The Taylor box is widened by the remainder bound
taken at `A.absMax`, so the tail bound is checkable from the interval matrix alone rather than
at whichever member of it a step turns out to hold.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Taylor box widened by the remainder bound taken at `A.absMax`, so the
tail bound is checkable from the interval matrix alone rather than at whichever
member of it a step turns out to hold. -/
noncomputable def MatExp.expIntervalEnclosure (A : Interval (Mat ℝ n n)) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun i j => (MatExp.expIntervalTaylor A η).inf i j
    - MatExp.expRemainderBound A.absMax η
  sup := fun i j => (MatExp.expIntervalTaylor A η).sup i j
    + MatExp.expRemainderBound A.absMax η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
