module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.OrderAdmissible

@[expose] public section

/-!
# Choosing the truncation order from an admissible error

`expRemainderOrder`: [1] tunes a reachability run's parameters to an error the caller states
rather than to numbers the caller guesses. Given `ε`, `expRemainderOrder` names the least order
whose remainder bound is under `ε`, so it is a tuning rule and not an arbitrary pick. `sInf` over
ℕ is `Nat.find` under classical decidability, which makes it noncomputable: no `Decidable`
instance for a strict inequality between reals exists at this layer. **`ε` is one term of a
step's error and not all of it.** `LinearSys.timePointStepError` bounds how far a step's
enclosure exceeds what the step reaches; `expRemainderBound` is one of its two parts, and
shortening the step reaches both (`exists_timePointStepError_lt`), which [1] tunes.

## Inputs
* `x` – matrix
* `ε` – admissible error

## Output
* least order whose remainder bound is under the error

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

/-- The least order meeting `ε`, and `0` where none does — which `0 < ε` rules
out, `expRemainderOrder_spec` being stated under exactly that. -/
noncomputable def MatExp.expRemainderOrder (x : Mat ℝ n n) (ε : ℝ) : ℕ :=
  sInf {η : ℕ | MatExp.OrderAdmissible x ε η}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
