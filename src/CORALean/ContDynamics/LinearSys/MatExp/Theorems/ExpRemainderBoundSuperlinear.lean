module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `expRemainderBound` shrinks superlinearly in its argument

Sharper than `expRemainderBound_mono`: scaling `x` down by `φ ∈ (0,1)` does not
merely shrink the bound, it shrinks it by at least the same factor `φ`. The
leading term picks up `φ^(η+1) ≤ φ`, and the geometric factor only helps
further, since a smaller argument shrinks its own denominator less.

`hx` is stated at `x`, the larger argument, and is what `Enclosures.lean`'s
side condition already asks for — `φ • x` needs no separate check, `φ < 1`
carrying it down automatically.

## Inputs
* `x` – matrix
* `η` – Taylor order
* `φ` – scale factor

## Hypotheses
* `hφ0` – scale factor positive
* `hφ1` – scale factor below one
* `hx` – norm small enough for the Taylor order

## Conclusion
* scaling the argument scales the bound down by at least the factor
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Scaling the argument by `φ ∈ (0,1)` scales the bound down by at least `φ`. -/
theorem MatExp.expRemainderBound_superlinear {x : Mat ℝ n n} (η : ℕ) {φ : ℝ}
    (hφ0 : 0 < φ) (hφ1 : φ < 1) (hx : ‖x‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    MatExp.expRemainderBound (φ • x) η ≤ φ * MatExp.expRemainderBound x η := by -- --- PROOF ---
  have hnormx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have hnormsmul : ‖φ • x‖ = φ * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hφ0]
  have hxφ_le : φ * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left hnormx hφ1.le
  have hfrac_le : (φ * ‖x‖) / ((η : ℝ) + 2) ≤ ‖x‖ / ((η : ℝ) + 2) := by gcongr
  have hdx : (0 : ℝ) < 1 - ‖x‖ / ((η : ℝ) + 2) := by linarith
  have hdxφ : (0 : ℝ) < 1 - (φ * ‖x‖) / ((η : ℝ) + 2) := by linarith
  -- a smaller argument leaves a larger geometric factor, capped by the one at `x`
  have hinv_le : (1 - (φ * ‖x‖) / ((η : ℝ) + 2))⁻¹ ≤ (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ :=
    inv_anti₀ hdx (by linarith)
  have hA_nonneg : (0 : ℝ) ≤ (1 - (φ * ‖x‖) / ((η : ℝ) + 2))⁻¹ := inv_nonneg.mpr hdxφ.le
  have hpow_le_one : φ ^ η ≤ 1 := pow_le_one₀ hφ0.le hφ1.le
  have hstep : φ ^ η * (1 - (φ * ‖x‖) / ((η : ℝ) + 2))⁻¹ ≤ (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ :=
    ((mul_le_mul_of_nonneg_right hpow_le_one hA_nonneg).trans_eq (one_mul _)).trans hinv_le
  have hstep2 : φ ^ (η + 1) * (1 - (φ * ‖x‖) / ((η : ℝ) + 2))⁻¹
      ≤ φ * (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hstep hφ0.le
    rwa [← mul_assoc, ← pow_succ'] at h
  have ha_nonneg : (0 : ℝ) ≤ ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := by positivity
  -- both bounds are that same numerator times one of the two geometric factors above
  have heq1 : MatExp.expRemainderBound (φ • x) η
      = φ ^ (η + 1) * (1 - (φ * ‖x‖) / ((η : ℝ) + 2))⁻¹
        * (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) := by
    simp only [MatExp.expRemainderBound, hnormsmul, mul_pow]
    ring
  have heq2 : φ * (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ * (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ))
      = φ * MatExp.expRemainderBound x η := by
    simp only [MatExp.expRemainderBound]
    ring
  calc MatExp.expRemainderBound (φ • x) η
      = φ ^ (η + 1) * (1 - (φ * ‖x‖) / ((η : ℝ) + 2))⁻¹
          * (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) := heq1
    _ ≤ φ * (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ * (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_right hstep2 ha_nonneg
    _ = φ * MatExp.expRemainderBound x η := heq2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
