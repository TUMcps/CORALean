module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

@[expose] public section

/-!
# An admissible truncation order

`OrderAdmissible`: [1]'s admissibility spec for the truncation order: an order meeting the
admissible error `ε` at `x`, at least `2`, its bound under `ε`, and the side condition that
makes that bound mean anything.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An order meeting the admissible error `ε` at `x`: at least `2`, its bound
under `ε`, and the side condition that makes that bound mean anything. -/
def MatExp.OrderAdmissible (x : Mat ℝ n n) (ε : ℝ) (η : ℕ) : Prop :=
  2 ≤ η ∧ MatExp.expRemainderBound x η < ε ∧ ‖x‖ / ((η : ℝ) + 2) < 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
