module

public import CORALean.ContSet.Interval.Real.Operations.MatPow
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# Interval matrices: the Taylor series past order two

`expIntervalTaylorTail`: orders `3 … κ` of [1, Thm. 1]'s Taylor series at an interval
matrix, by ordinary interval arithmetic, each power formed as `B·Bᵏ` (`Interval.matPow`) where [1]
multiplies left to right, `((BB)…B)`. Below order three there are none — `point 0` rather
than undefined, so `κ < 3` is the truncation `I + W(t)` and not a special case.

## Inputs
* `B` – interval matrix

## Output
* interval matrix of the Taylor terms from order three up to the given order

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Sonnet 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
