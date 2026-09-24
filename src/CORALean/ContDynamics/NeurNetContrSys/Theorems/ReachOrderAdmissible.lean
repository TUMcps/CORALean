import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachOrder

/-!
# `reachOrder` clears `reach_outer`'s side condition

`Nat.le_ceil` puts `‖Δt • A‖` at or under `reachOrder Δt`, strictly under the
denominator once `2` is added — `LinearSys.reachOrder_admissible`'s argument,
one `+ 2` short since `reach_outer` asks for none on the numerator's side.
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
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.reachOrder_admissible (sys : NeurNetContrSys 𝕋 S n) (Δt : ℝ) :
    ‖Δt • toRealMat sys.plant.A‖ / ((sys.reachOrder Δt : ℝ) + 2) < 1 := by
  have hle : ‖Δt • toRealMat sys.plant.A‖ ≤ (sys.reachOrder Δt : ℝ) := Nat.le_ceil _
  have hpos : (0:ℝ) < (sys.reachOrder Δt : ℝ) + 2 := by positivity
  rw [div_lt_one hpos]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
