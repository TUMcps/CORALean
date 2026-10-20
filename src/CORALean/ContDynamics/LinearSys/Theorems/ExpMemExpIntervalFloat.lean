module

public import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# `e^{At}` lies in `expIntervalFloat` at every time of its range

`t • A` is in `[tLo, tHi] · A` by `Interval.smul_outer`, the stored matrix being
in its own point interval, and `MatExp.exp_mem_expIntervalEnclosure` does the
rest at an admissible order. No sign is asked of `t`: a range straddling zero is
enclosed as soundly as a positive one.

## Inputs
* `sys` – linear system
* `tLo` – lower time bound
* `tHi` – upper time bound
* `η` – Taylor order
* `t` – time

## Hypotheses
* `hη` – order admissible
* `htLo` – time at least the lower bound
* `htHi` – time at most the upper bound

## Conclusion
* the exponential at the time lies in the float interval enclosure
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


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
