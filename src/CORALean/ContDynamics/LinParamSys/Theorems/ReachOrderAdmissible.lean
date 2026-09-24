import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder

/-!
# `reachOrder` clears `timeIntervalStep_outer`'s side condition

`LinearSys.reachOrder_admissible`'s argument, `Nat.le_ceil` putting the bound
at or under `reachOrder r`, strictly under the denominator once `4` is added.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.reachOrder_admissible (sys : LinParamSys ℐ n) (r : ℝ) :
    ‖(Interval.smul r sys.A).absMax‖
      / (((sys.reachOrder r + 2 : ℕ) : ℝ) + 2) < 1 := by -- --- PROOF ---
  have hle : ‖(Interval.smul r sys.A).absMax‖ ≤ (sys.reachOrder r : ℝ) := Nat.le_ceil _
  have hpos : (0:ℝ) < ((sys.reachOrder r + 2 : ℕ) : ℝ) + 2 := by positivity
  rw [div_lt_one hpos]
  push_cast
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
