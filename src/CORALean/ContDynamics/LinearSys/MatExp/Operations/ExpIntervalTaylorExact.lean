module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorTail
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalW

@[expose] public section

/-!
# Interval matrices: the Taylor truncation with an exact second order

`expIntervalTaylorExact`: the truncation of [1, Thm. 1]: the identity and `W(t)` exactly,
the rest by interval arithmetic.

## Inputs
* `A` – interval matrix
* `t` – time
* `κ` – Taylor order

## Output
* Taylor truncation with exact identity and second-order term

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The truncation of [1, Thm. 1]: the identity and `W(t)` exactly, the rest
by interval arithmetic. -/
noncomputable def MatExp.expIntervalTaylorExact (A : Interval (Mat ℝ n n)) (t : ℝ)
    (κ : ℕ) : Interval (Mat ℝ n n) :=
  Interval.plus (Interval.plus (Interval.point 1) (MatExp.expIntervalW A t))
    (MatExp.expIntervalTaylorTail (Interval.smul t A) κ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
