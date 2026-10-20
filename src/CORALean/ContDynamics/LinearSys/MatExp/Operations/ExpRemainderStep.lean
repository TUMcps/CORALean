module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.StepAdmissible

@[expose] public section

/-!
# Choosing the step size from an admissible error

`expRemainderStep`: the second knob of [1], the way `expRemainderOrder` is the first: given an order
and an admissible error `ε`, it names a positive step whose contribution
`r · expRemainderBound (r • A) η` (the radius of `inputRemainder`) stays under `ε`, and whose side
condition holds too. `Classical.choose` rather than a least element: the admissible steps are an
interval open at `0`, so there is no least one to name. Where no step meets `ε`, which `0 < ε` rules
out, the junk branch is `1`. **`ε` is one term of a step's error and not all of it:**
`exists_timePointStepError_lt` names a step at which the *whole* `LinearSys.timePointStepError` is
under a stated bound, where no order can. [1] tunes both, and the zonotope order besides.

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

open scoped Classical in
/-- A step meeting `ε` at order `η`, and `1` where none does — which `0 < ε`
rules out, `expRemainderStep_spec` being stated under exactly that. -/
noncomputable def MatExp.expRemainderStep (A : Mat ℝ n n) (η : ℕ) (ε : ℝ) : ℝ :=
  if h : ∃ r : ℝ, MatExp.StepAdmissible A η ε r then h.choose else 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
