import CORALean.ContDynamics.LinearSys.MatExp.Definitions.OrderAdmissible
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderOrder

/-!
# The chosen order is the least admissible one

What makes `expRemainderOrder` a tuning rule rather than an arbitrary choice:
no admissible order is smaller, so the truncation is as cheap as the stated
error allows.

Needs no hypothesis on `ε`: an admissible `η` in hand is itself the witness
that the set is inhabited, so the empty-set branch of `sInf` cannot be the one
taken.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Minimality: every order meeting `ε` is at least the one chosen for it. -/
theorem MatExp.expRemainderOrder_le {x : Mat ℝ n n} {ε : ℝ} {η : ℕ}
    (h : MatExp.OrderAdmissible x ε η) : MatExp.expRemainderOrder x ε ≤ η :=
  Nat.sInf_le h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
