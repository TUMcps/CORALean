module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe

@[expose] public section

/-!
# The exponential's remainder is within the step's bound at every entry

The bound grows with `‖τ • A‖`, so the value taken at the end of the step covers
every time inside it: one interval matrix of uniform width holds the remainder
over all of `[0, r]`, which is what an input solution multiplies its input set
by.

Entrywise, an entry never exceeding the norm — the bound is on a norm, and
nothing sharper per entry is available.

## Inputs
* `A` – system matrix
* `r` – step length
* `τ` – time
* `η` – Taylor order
* `j` – row index
* `k` – column index

## Hypotheses
* `hr` – step length positive
* `hτ0` – time nonnegative
* `hτr` – time within the step
* `hε` – scaled norm small enough for the Taylor order

## Conclusion
* every entry of the remainder is within the step's bound
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

/-- Every entry of the remainder is within the step's bound, uniformly over the
step. -/
theorem MatExp.remainder_entry_le (A : Mat ℝ n n) {r τ : ℝ} (η : ℕ) (hr : 0 < r)
    (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hε : ‖r • A‖ / ((η : ℝ) + 2) < 1) (j k : Fin n) :
    |(exp (τ • A) - MatExp.expTaylor (τ • A) η) j k|
      ≤ MatExp.expRemainderBound (r • A) η := by -- --- PROOF ---
  have hnorm : ‖τ • A‖ ≤ ‖r • A‖ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hτ0,
      abs_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_right hτr (norm_nonneg A)
  have hετ : ‖τ • A‖ / ((η : ℝ) + 2) < 1 := by
    have h2 : (0:ℝ) < (η : ℝ) + 2 := by positivity
    calc ‖τ • A‖ / ((η : ℝ) + 2) ≤ ‖r • A‖ / ((η : ℝ) + 2) := by gcongr
      _ < 1 := hε
  calc |(exp (τ • A) - MatExp.expTaylor (τ • A) η) j k|
      ≤ ‖exp (τ • A) - MatExp.expTaylor (τ • A) η‖ := abs_entry_le_norm _ j k
    _ ≤ MatExp.expRemainderBound (τ • A) η := norm_exp_sub_expTaylor_le _ η hετ
    _ ≤ MatExp.expRemainderBound (r • A) η := MatExp.expRemainderBound_mono η hnorm hε

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
