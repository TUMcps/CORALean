import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import Mathlib.Tactic.Positivity

/-!
# `expRemainderBound` decreases order by order

Raising `η` by one shrinks the truncated tail's leading term and the geometric
factor alike, given the side condition at `η` — which then also holds at
`η + 1`, since `‖x‖/(η + 3) ≤ ‖x‖/(η + 2)`. A step at a time, not a general
`Antitone`: the successor case is all the tuning algorithm needs.
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

/-- One more order never costs precision: raising `η` never raises the bound,
given the side condition the lower order already needs. -/
theorem MatExp.expRemainderBound_antitone_succ {x : Mat ℝ n n} (η : ℕ)
    (hx : ‖x‖ / ((η : ℝ) + 2) < 1) :
    MatExp.expRemainderBound x (η + 1) ≤ MatExp.expRemainderBound x η := by -- --- PROOF ---
  have hnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have h2pos : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  have hterm1_nn : (0 : ℝ) ≤ ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := by positivity
  have hfact : (Nat.factorial (η + 1 + 1) : ℝ) = ((η : ℝ) + 2) * (Nat.factorial (η + 1) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have heq : ‖x‖ ^ (η + 1 + 1) / (Nat.factorial (η + 1 + 1) : ℝ)
      = (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * (‖x‖ / ((η : ℝ) + 2)) := by
    rw [hfact, pow_succ]
    field_simp
  -- the leading term shrinks by a factor of at most `1`, the side condition's own bound
  have hterm1 : ‖x‖ ^ (η + 1 + 1) / (Nat.factorial (η + 1 + 1) : ℝ)
      ≤ ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := by
    rw [heq]
    calc (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * (‖x‖ / ((η : ℝ) + 2))
        ≤ (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hx.le hterm1_nn
      _ = ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := mul_one _
  have hfrac_mono : ‖x‖ / ((η : ℝ) + 1 + 2) ≤ ‖x‖ / ((η : ℝ) + 2) := by
    apply div_le_div_of_nonneg_left hnn h2pos
    linarith
  have hd1 : (0 : ℝ) < 1 - ‖x‖ / ((η : ℝ) + 2) := by linarith
  have hd2 : (0 : ℝ) < 1 - ‖x‖ / ((η : ℝ) + 1 + 2) := by linarith
  have hterm2 : (1 - ‖x‖ / ((η : ℝ) + 1 + 2))⁻¹ ≤ (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ :=
    inv_anti₀ hd1 (by linarith)
  have hterm2_nn : (0 : ℝ) ≤ (1 - ‖x‖ / ((η : ℝ) + 1 + 2))⁻¹ := inv_nonneg.mpr hd2.le
  simp only [MatExp.expRemainderBound]
  push_cast
  exact mul_le_mul hterm1 hterm2 hterm2_nn hterm1_nn

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
