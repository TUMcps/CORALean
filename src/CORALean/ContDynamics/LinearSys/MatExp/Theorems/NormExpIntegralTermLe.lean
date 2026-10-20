module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# One order of the integrated exponential, in terms of the exponential's own

`expIntegral` is the exponential integrated once over `[0, r]`, so its order `i` carries
`r^{i+1}/(i+1)!` where the exponential carries `r^i/i!`. One factor of `r` comes out in front and
what is left is the exponential's order `i` at `r A`, which is why `inputRemainder`'s radius is
`r · expRemainderBound (r A) η` and not a bound of its own. The extra factorial is dropped:
`(i+1)! ≥ i!` makes this the exponential's order at the same index and not a tighter one, which
the step size in front already pays for. Only orders `1` and up, `‖A^i‖ ≤ ‖A‖^i` being false at
`i = 0`, where the power is the identity and the operator norm bounds nothing.

## Inputs
* `A` – system matrix
* `r` – step length
* `j` – order index

## Hypotheses
* `hr` – step length nonnegative
* `hj` – order at least one

## Conclusion
* one integrated term is under the step times the exponential's own term
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- One order of the integrated series, under the step times the exponential's
own order. -/
theorem MatExp.norm_expIntegralTerm_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 ≤ r) {j : ℕ}
    (hj : 1 ≤ j) :
    ‖((Nat.factorial (j + 1) : ℝ)⁻¹ * r ^ (j + 1)) • A ^ j‖
      ≤ r * ((Nat.factorial j : ℝ)⁻¹ * ‖r • A‖ ^ j) := by -- --- PROOF ---
  have hfac : (0:ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfacle : (Nat.factorial j : ℝ) ≤ (Nat.factorial (j + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ j)
  have hnorm : ‖r • A‖ = r * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  have hsplit : ‖((Nat.factorial (j + 1) : ℝ)⁻¹ * r ^ (j + 1)) • A ^ j‖
      = ((Nat.factorial (j + 1) : ℝ)⁻¹ * r ^ (j + 1)) * ‖A ^ j‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg hr _))]
  rw [hsplit, hnorm, mul_pow]
  -- the extra factorial is dropped and `A`'s power leaves the norm
  have hstep : ((Nat.factorial (j + 1) : ℝ)⁻¹ * r ^ (j + 1)) * ‖A ^ j‖
      ≤ ((Nat.factorial j : ℝ)⁻¹ * r ^ (j + 1)) * ‖A‖ ^ j := by
    refine mul_le_mul ?_ (norm_pow_le' A hj) (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right (by gcongr) (pow_nonneg hr _)
  refine hstep.trans (le_of_eq ?_)
  rw [pow_succ]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
