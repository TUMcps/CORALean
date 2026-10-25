module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# The matrix exponential's Taylor remainder, bounded

`expRemainderBound`: [1, Thm. 1] — what the neglected terms of `expTaylor` can still amount
to, the radius of `expEnclosure`. Sound only under `‖x‖ / (η + 2) < 1`; without it the geometric
bound diverges and this is meaningless rather than merely loose.

## Inputs
* `x` – matrix
* `η` – Taylor order

## Output
* bound on the Taylor remainder

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the neglected terms can still amount to, which is the radius. Sound
only under `‖x‖ / (η + 2) < 1`; without it the geometric bound diverges and this
is meaningless rather than merely loose. -/
noncomputable def MatExp.expRemainderBound (x : Mat ℝ n n) (η : ℕ) : ℝ :=
  (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
