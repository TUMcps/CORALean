module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrTerm
public import CORALean.ContSet.Interval.Real.Operations.AbsMax

@[expose] public section

/-!
# Interval matrices: the correction matrix over a box

`intervalCorrectionMatrix`: [1, Thm. 3]'s `F` over a whole box: orders `2` through `η` from
`intervalCorrTerm`, everything past `η` in the tail bound at `r • A`, and indexed from `2`
exactly as the point case is.

## Inputs
* `A` – interval matrix
* `r` – step length
* `η` – Taylor order

## Output
* interval matrix of the correction over the box

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". In Proc. of the 46th IEEE Conference on Decision and Control (CDC),
      2007, pp. 726-732.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of [1, Thm. 3] over a whole box: orders `2` through `η` from
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
