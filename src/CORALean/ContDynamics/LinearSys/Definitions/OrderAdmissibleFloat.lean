import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Operations.Smul

/-!
# A Taylor order the float enclosures of `e^{At}` admit over a time range

The float remainder `MatExp.expRemainderBound` is sound once `nrm / (η + 2) ≤ 1/2`,
`nrm` a float bound on `‖t A‖` over every `t ∈ [tLo, tHi]` — here the one
`MatExp.normUpperBound` reads off the interval matrix `[tLo, tHi] · A`. Its
geometric factor is the fixed constant `2`, which is where `1/2` comes from
where the exact layer's `timeIntervalStep_outer` asks `< 1`. At least `2`, as
`MatExp.intervalCorrectionMatrix`'s guarantee needs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `η` is at least `2` and the float remainder bound at `[tLo, tHi] · A` is
sound at it. -/
def LinearSys.OrderAdmissibleFloat (sys : LinearSys 𝕋 n) (tLo tHi : 𝕋) (η : ℕ) : Prop :=
  2 ≤ η ∧ toReal (MatExp.normUpperBound (Interval.smul tLo tHi (Interval.point sys.A)))
    / ((η : ℝ) + 2) ≤ 1 / 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
