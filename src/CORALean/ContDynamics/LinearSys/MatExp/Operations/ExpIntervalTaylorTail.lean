import CORALean.ContSet.Interval.Real.Operations.MatPow
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Operations.Smul

/-!
# Interval matrices: the Taylor series past order two

`expIntervalTaylorTail`: orders `3 … κ` of [1, Thm. 3.2]'s Taylor series at an interval
matrix, by ordinary interval arithmetic. Below order three there are none — `point 0` rather
than undefined, so `κ < 3` is the truncation `I + W(t)` and not a special case.

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

/-- Orders `3 … κ` of the Taylor series at an interval matrix, by ordinary
interval arithmetic. Below order three there are none. -/
noncomputable def MatExp.expIntervalTaylorTail (B : Interval (Mat ℝ n n)) :
    ℕ → Interval (Mat ℝ n n)
  | 0 => Interval.point 0
  | 1 => Interval.point 0
  | 2 => Interval.point 0
  | k + 3 => Interval.plus
      (Interval.smul ((Nat.factorial (k + 3) : ℝ)⁻¹) (Interval.matPow B (k + 3)))
      (MatExp.expIntervalTaylorTail B (k + 2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
