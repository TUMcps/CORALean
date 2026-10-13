import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpNormUpFloat

/-!
# `expNormUpFloat` bounds `e^{nrm}`

At an admissible order `nrm ≤ (η + 2)/2 < 2^{log₂(η+2)+1}/2`, which is inside `expUp`'s range
at `p = log₂(η + 2) + 5`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^{nrm} ≤ expNormUpFloat r η`, `nrm` the float bound on `‖r A‖`, at an admissible `η`. -/
theorem LinearSys.exp_le_expNormUpFloat (sys : LinearSys 𝕋 n) {r : 𝕋} {η : ℕ}
    (hη : sys.OrderAdmissibleFloat r r η) :
    Real.exp (toReal (MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A))))
      ≤ toReal (sys.expNormUpFloat r η) := by -- --- PROOF ---
  refine le_expUp _ _ ?_
  have h2 : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  have hle : toReal (MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A)))
      ≤ ((η : ℝ) + 2) / 2 := by
    have := hη.2
    rw [div_le_iff₀ h2] at this
    linarith
  have hlt : ((η + 2 : ℕ) : ℝ) < 2 ^ (Nat.log2 (η + 2) + 1) := by
    exact_mod_cast Nat.lt_log2_self
  have hmono : (2 : ℝ) ^ (Nat.log2 (η + 2) + 1) ≤ 2 ^ (Nat.log2 (η + 2) + 5) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  push_cast at hlt
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
