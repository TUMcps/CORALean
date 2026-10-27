module

public import CORALean.ContDynamics.NonlinearSys.Theorems.ShearPowEqZero
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

/-!
# The exponential of the shear

For the linearization `A = [0 1; 0 0]` of the shear `ẋ = (x₂, 0)`, `A² = 0`, so the series of
`e^{AΔt}` stops after its linear term: `e^{AΔt} = I + AΔt`, the `e^{AΔt}` of (11) in the
convex counterexample to [1, Prop. 2].

## Inputs
* `Δt` – time

## Hypotheses
* none

## Conclusion
* the exponential is identity plus the scaled matrix

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^{AΔt} = I + AΔt` for the shear `A = [0 1; 0 0]`. -/
theorem NonlinearSys.exp_smul_shear (Δt : ℝ) : -- --- CONCL ---
    exp (Δt • (!![0, 1; 0, 0] : Mat ℝ 2 2)) = 1 + Δt • !![0, 1; 0, 0] := by -- --- PROOF ---
  rw [exp_eq_tsum ℝ]
  show ∑' i : ℕ, ((i.factorial : ℝ)⁻¹) • (Δt • (!![0, 1; 0, 0] : Mat ℝ 2 2)) ^ i = _
  rw [tsum_eq_sum (s := Finset.range 2) fun b hb => by
    rw [smul_pow, NonlinearSys.shear_pow_eq_zero (by simp at hb; omega), smul_zero, smul_zero]]
  simp [Finset.sum_range_succ]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
