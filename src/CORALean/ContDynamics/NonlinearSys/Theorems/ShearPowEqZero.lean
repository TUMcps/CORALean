module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
# The shear matrix is nilpotent

The linearization `A = [0 1; 0 0]` of the shear `ẋ = (x₂, 0)`, the field of the convex
counterexample to [1, Prop. 2], squares to `0`, so every power `Aⁱ`, `i ≥ 2`, vanishes: the
Taylor series of `e^{AΔt}` and the sums (13), (17) of [1] built from it stop after their linear
terms.

## Inputs
* `i` – exponent

## Hypotheses
* `hi` – exponent at least two

## Conclusion
* the power of the shear matrix is zero

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Aⁱ = 0` for the shear `A = [0 1; 0 0]` and `i ≥ 2`. -/
theorem NonlinearSys.shear_pow_eq_zero {i : ℕ} (hi : 2 ≤ i) :
    (!![0, 1; 0, 0] : Mat ℝ 2 2) ^ i = 0 :=
  pow_eq_zero_of_le hi (by
    ext j k; fin_cases j <;> fin_cases k <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
