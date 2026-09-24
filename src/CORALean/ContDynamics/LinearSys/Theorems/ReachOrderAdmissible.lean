import CORALean.ContDynamics.LinearSys.Operations.ReachOrder

/-!
# `reachOrder` clears `timeIntervalStep_outer`'s side condition

`Nat.le_ceil` puts `‖r • A‖` at or under `reachOrder r`, so adding `4` puts it
strictly under the denominator `timeIntervalStep_outer` divides by, at `m :=
reachOrder r`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachOrder_admissible (sys : LinearSys 𝕋 n) (r : ℝ) :
    ‖r • toRealMat sys.A‖ / (((sys.reachOrder r + 2 : ℕ) : ℝ) + 2) < 1 := by -- --- PROOF ---
  have hle : ‖r • toRealMat sys.A‖ ≤ (sys.reachOrder r : ℝ) := Nat.le_ceil _
  have hpos : (0:ℝ) < ((sys.reachOrder r + 2 : ℕ) : ℝ) + 2 := by positivity
  rw [div_lt_one hpos]
  push_cast
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
