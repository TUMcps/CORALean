module

public import CORALean.ContDynamics.LinearSys.Operations.ReachOrder
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `reachOrder` clears `timeInterval_outer`'s side condition

`Nat.le_ceil` puts `‖r • A‖` at or under `reachOrder r`, so any order `η` at or
above `reachOrder r + 2` puts it strictly under `η + 2`, the denominator
`timeInterval_outer` divides by. `reach` raises its `η` to exactly such one.

## Inputs
* `sys` – linear system
* `r` – window width
* `η` – Taylor order

## Hypotheses
* `hη` – order at least the chosen reach order plus two

## Conclusion
* the scaled norm is small enough for the order
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachOrder_admissible (sys : LinearSys 𝕋 n) (r : ℝ) {η : ℕ}
    (hη : sys.reachOrder r + 2 ≤ η) : -- --- CONCL ---
    ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1 := by -- --- PROOF ---
  have hle : ‖r • toRealMat sys.A‖ ≤ (sys.reachOrder r : ℝ) := Nat.le_ceil _
  have hη' : ((sys.reachOrder r + 2 : ℕ) : ℝ) ≤ η := by exact_mod_cast hη
  have hpos : (0:ℝ) < (η : ℝ) + 2 := by positivity
  rw [div_lt_one hpos]
  push_cast at hη'
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
