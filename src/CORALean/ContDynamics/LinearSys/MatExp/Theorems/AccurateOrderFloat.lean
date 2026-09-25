import CORALean.ContDynamics.LinearSys.MatExp.Operations.AccurateOrderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AccurateOrderFromFloat

/-!
# An order `accurateOrder` returns is admissible and meets the tolerance

`accurateOrderFrom_spec` at the values `accurateOrder` starts the loop with,
and `le`'s `true` is sound. The first test is `admissibleOrder_spec`'s argument
again: `half` is exact and the count is rounded down, so `nrm ≤ (η + 2)/2`.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.accurateOrder_spec {nrm tol : 𝕋} {η₀ fuel η : ℕ}
    (h : MatExp.accurateOrder nrm tol η₀ fuel = some η) :
    toReal nrm / ((η : ℝ) + 2) ≤ 1 / 2 ∧ η₀ ≤ η
      ∧ toReal (MatExp.expRemainderBound nrm η) ≤ toReal tol := by -- --- PROOF ---
  obtain ⟨hadm, hle, htol⟩ := MatExp.accurateOrderFrom_spec rfl rfl rfl h
  refine ⟨?_, hle, toReal_le_of_le htol⟩
  -- `half` is exact and the count is rounded down, so `nrm ≤ (η + 2)/2`
  have hle' := toReal_le_of_le hadm
  have hcount := nsmulDown_le (η + 2) (one : 𝕋)
  rw [toReal_one, mul_one] at hcount
  rw [toReal_half] at hle'
  have hpos : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  rw [div_le_iff₀ hpos]
  push_cast at hcount
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
