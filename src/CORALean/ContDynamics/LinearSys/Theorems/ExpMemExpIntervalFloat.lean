import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContSet.Interval.Float.Theorems.MemPoint
import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

/-!
# `e^{At}` lies in `expIntervalFloat` at every time of its range

`t • A` is in `[tLo, tHi] · A` by `Interval.smul_outer`, the stored matrix being
in its own point interval, and `MatExp.exp_mem_expIntervalEnclosure` does the
rest at an admissible order. No sign is asked of `t`: a range straddling zero is
enclosed as soundly as a positive one.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.exp_mem_expIntervalFloat (sys : LinearSys 𝕋 n) {tLo tHi : 𝕋} {η : ℕ}
    (hη : sys.OrderAdmissibleFloat tLo tHi η) {t : ℝ} (htLo : toReal tLo ≤ t)
    (htHi : t ≤ toReal tHi) :
    exp (t • Scalar.toRealMat sys.A) ∈ (sys.expIntervalFloat tLo tHi η).construct := by
  rw [LinearSys.expIntervalFloat, Interval.materialiseMat_eq]
  exact MatExp.exp_mem_expIntervalEnclosure _ η
    (Interval.smul_outer htLo htHi _ (Interval.mem_point sys.A)) hη.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
