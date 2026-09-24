import CORALean.ContSet.Interval.Real.Interval

/-!
# The matrix exponential's Taylor remainder, bounded

`expRemainderBound`: [1, Eq. 3.2–3.3] — what the neglected terms of `expTaylor` can still amount
to, the radius of `expEnclosure`. Sound only under `‖x‖ / (η + 2) < 1`; without it the geometric
bound diverges and this is meaningless rather than merely loose.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


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
