module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContSet.Interval.Real.Operations.AbsMax

@[expose] public section

/-!
# Interval matrices: enclosing the exponential of an interval matrix

`expIntervalEnclosure`: the enclosure of [1, Thm. 1] at a whole box with every order by interval
arithmetic, the exact `W(t)` of [1, Lemma 1] left out: `expTaylor`/`expEnclosure` at one matrix,
widened to bound every matrix a whole box could hold. The Taylor box is widened by the remainder
bound taken at `A.absMax`, so the tail bound is checkable from the interval matrix alone rather than
at whichever member of it a step turns out to hold.

## Inputs
* `A` – interval matrix
* `η` – Taylor order

## Output
* interval matrix enclosing the exponential of every member

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
