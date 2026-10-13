import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The matrix exponential's Taylor truncation

`expTaylor`: [1, Eq. 3.2–3.3]'s series truncated at `η`, the centre of the enclosure
`expEnclosure` builds around `exp x`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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

/-- The series truncated at `η`, which is the centre of the enclosure. -/
noncomputable def MatExp.expTaylor (x : Mat ℝ n n) (η : ℕ) : Mat ℝ n n :=
  ∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹) • x ^ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
