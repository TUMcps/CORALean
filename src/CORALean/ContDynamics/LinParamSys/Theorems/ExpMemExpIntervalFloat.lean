module

public import CORALean.ContDynamics.LinParamSys.Definitions.OrderAdmissibleFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureFloat
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# `e^{At}` lies in `expIntervalFloat` at every member and every time of its range

`LinearSys.exp_mem_expIntervalFloat` with the member `A ∈ sys.A` in place of
the stored point: `t • A` is in `[tLo, tHi] · sys.A` by `Interval.smul_outer`,
and `MatExp.exp_mem_expIntervalEnclosure` does the rest at an admissible order.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.exp_mem_expIntervalFloat
    (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n) {tLo tHi : 𝕋} {η : ℕ}
    (hη : sys.OrderAdmissibleFloat tLo tHi η) {A : Mat ℝ n n} (hA : A ∈ sys.A.construct)
    {t : ℝ} (htLo : toReal tLo ≤ t) (htHi : t ≤ toReal tHi) :
    exp (t • A) ∈ (sys.expIntervalFloat tLo tHi η).construct := by -- --- PROOF ---
  rw [LinParamSys.expIntervalFloat, Interval.materialiseMat_eq]
  exact MatExp.exp_mem_expIntervalEnclosure _ η (Interval.smul_outer htLo htHi _ hA) hη.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
