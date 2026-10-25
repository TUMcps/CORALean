module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# Interval matrices: the input remainder of a box

`intervalInputRemainder`: the `E(r)·r` of [1, Prop. 2] over a whole box: one width for every entry
and every member, the tail bound being on a norm.

The tail is taken at a dominating matrix for the reason `ExpIntervalEnclosure`
gives — checkable from the box alone, before a member is fixed — and at `r • A`,
so one condition serves this, the exponential enclosure, and (`r`-scaled) the
constant correction's own tail all at once.

## Inputs
* `A` – interval matrix
* `r` – step length
* `η` – Taylor order

## Output
* interval matrix of the input remainder over the box

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `E(r)·r` of [1, Prop. 2] over a whole box: one width for every entry and every
member, the tail bound being on a norm. -/
noncomputable def MatExp.intervalInputRemainder (A : Interval (Mat ℝ n n)) (r : ℝ)
    (η : ℕ) : Interval (Mat ℝ n n) where
  inf := fun _ _ => -(r * MatExp.expRemainderBound (Interval.smul r A).absMax η)
  sup := fun _ _ => r * MatExp.expRemainderBound (Interval.smul r A).absMax η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
