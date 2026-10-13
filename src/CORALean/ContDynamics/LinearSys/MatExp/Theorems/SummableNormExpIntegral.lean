module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# The integrated series is dominated by the exponential's own

`expIntegral` differs from the exponential series only in carrying one more
power of `t` against a factorial one step further along, so it converges
wherever the exponential does — and the comparison needs nothing about `A`
beyond `‖A^i‖ ≥ 0`.

Bounding `‖A^i‖` by `‖A‖^i` would be the obvious route and fails at `i = 0`:
that power is the identity, whose operator norm is `1` only when the dimension
is positive.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The integrated series is dominated by `|t|` times the exponential's own. -/
theorem MatExp.summable_norm_expIntegral (A : Mat ℝ n n) (t : ℝ) :
    Summable (fun i : ℕ => ‖(((Nat.factorial (i + 1) : ℝ))⁻¹ * t ^ (i + 1))
      • A ^ i‖) := by -- --- PROOF ---
  have hg : Summable
      (fun i : ℕ => |t| * ‖((Nat.factorial i : ℝ))⁻¹ • (t • A) ^ i‖) :=
    (norm_expSeries_summable' (𝕂 := ℝ) (t • A)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hg
  have hfi : (0:ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hfi1 : (0:ℝ) < (Nat.factorial (i + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (i + 1)
  have hle : (Nat.factorial i : ℝ) ≤ (Nat.factorial (i + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ i)
  rw [smul_pow, smul_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_inv, abs_inv, abs_pow, abs_pow, abs_of_pos hfi,
    abs_of_pos hfi1, pow_succ]
  calc ((Nat.factorial (i + 1) : ℝ))⁻¹ * (|t| ^ i * |t|) * ‖A ^ i‖
      ≤ ((Nat.factorial i : ℝ))⁻¹ * (|t| ^ i * |t|) * ‖A ^ i‖ := by gcongr
    _ = |t| * (((Nat.factorial i : ℝ))⁻¹ * |t| ^ i * ‖A ^ i‖) := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
