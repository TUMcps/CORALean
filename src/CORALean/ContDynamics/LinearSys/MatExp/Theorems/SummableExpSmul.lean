module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

@[expose] public section

/-!
# The series behind `exp (t • A)`, at the unscaled matrix, is summable

The same series `exp_smul_tsum` sums to, stated on its own: summability is
needed before its terms can be shifted or subtracted term by term, which is
what subtracting two such series in `ExpDiff` does.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem summable_exp_smul (A : Mat ℝ n n) (t : ℝ) :
    Summable (fun i : ℕ => (((Nat.factorial i : ℝ))⁻¹ * t ^ i) • A ^ i) := by
  have h := expSeries_summable' (𝕂 := ℝ) (t • A)
  refine h.congr fun i => ?_
  rw [smul_pow, smul_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
