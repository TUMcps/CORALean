import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrTerm
import CORALean.ContSet.Interval.Real.Operations.AbsMax
import CORALean.ContSet.Interval.Real.Operations.Smul

/-!
# Interval matrices: the integrated correction matrix over a box

`intervalConstCorrectionMatrix`: [1, Sec. 3.3.1]'s `F̃` over a whole box: orders `1` through
`η` from `intervalConstCorrTerm`, everything past `η` in the tail bound at `r • A` scaled by
`r`, and indexed exactly as the point case is.

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

/-- The `F̃` of [1] over a whole box: orders `1` through `η` from
`intervalConstCorrTerm`, everything past `η` in the tail bound at `r • A`
scaled by `r`, and indexed exactly as the point case is. -/
noncomputable def MatExp.intervalConstCorrectionMatrix (A : Interval (Mat ℝ n n)) (r : ℝ)
    (η : ℕ) : Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range η,
      min ((MatExp.intervalConstCorrTerm A r i).inf j k) 0)
    - r * MatExp.expRemainderBound (Interval.smul r A).absMax η
  sup := fun j k => (∑ i ∈ Finset.range η,
      max ((MatExp.intervalConstCorrTerm A r i).sup j k) 0)
    + r * MatExp.expRemainderBound (Interval.smul r A).absMax η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
