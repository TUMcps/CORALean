import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Data.Matrix.Mul

/-!
# The second-order Taylor term, exactly, at one matrix

`expW`: [1, Lemma 3.1]'s `W(t) = M t + ½ M² t²` at one matrix, which is orders one and two
of `expTaylor (t • M)`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `W(t) = M t + ½ M² t²` at one matrix, which is orders one and two of
`expTaylor (t • M)`. -/
noncomputable def MatExp.expW (M : Mat ℝ n n) (t : ℝ) : Mat ℝ n n :=
  t • M + (t ^ 2 / 2) • (M * M)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
