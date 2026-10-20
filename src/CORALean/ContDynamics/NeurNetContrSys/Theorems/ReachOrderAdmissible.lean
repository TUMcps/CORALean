module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachOrder
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `reachOrder` clears `reach_outer`'s side condition

`Nat.le_ceil` puts `‖Δt • A‖` at or under `reachOrder Δt`, strictly under the
denominator once `2` is added — `LinearSys.reachOrder_admissible`'s argument,
one `+ 2` short since `reach_outer` asks for none on the numerator's side.

## Inputs
* `sys` – closed-loop system
* `Δt` – step size

## Hypotheses
* none

## Conclusion
* the order is admissible for the step at the augmented matrix
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.reachOrder_admissible (sys : NeurNetContrSys (LinearSys 𝕋 n) S n) (Δt : ℝ) :
    ‖Δt • sys.augment.A‖ / ((sys.reachOrder Δt : ℝ) + 2) < 1 := by
  have hle : ‖Δt • sys.augment.A‖ ≤ (sys.reachOrder Δt : ℝ) := Nat.le_ceil _
  have hpos : (0:ℝ) < (sys.reachOrder Δt : ℝ) + 2 := by positivity
  rw [div_lt_one hpos]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
