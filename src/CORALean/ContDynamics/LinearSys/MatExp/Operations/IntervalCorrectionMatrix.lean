import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrTerm
import CORALean.ContSet.Interval.Real.Operations.AbsMax
import CORALean.ContSet.Interval.Real.Operations.Smul

/-!
# Interval matrices: the correction matrix over a box

`intervalCorrectionMatrix`: [1, Sec. 3.3.1]'s `F` over a whole box: orders `2` through `η` from
`intervalCorrTerm`, everything past `η` in the tail bound at `r • A`, and indexed from `2`
exactly as the point case is.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of [1] over a whole box: orders `2` through `η` from
`intervalCorrTerm`, everything past `η` in the tail bound at `r • A`, and
indexed from `2` exactly as the point case is. -/
noncomputable def MatExp.intervalCorrectionMatrix (A : Interval (Mat ℝ n n)) (r : ℝ)
    (η : ℕ) : Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range (η - 1),
      min ((MatExp.intervalCorrTerm A r (i + 2)).inf j k) 0)
    - MatExp.expRemainderBound (Interval.smul r A).absMax η
  sup := fun j k => (∑ i ∈ Finset.range (η - 1),
      max ((MatExp.intervalCorrTerm A r (i + 2)).sup j k) 0)
    + MatExp.expRemainderBound (Interval.smul r A).absMax η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
