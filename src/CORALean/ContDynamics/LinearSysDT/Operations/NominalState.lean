module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# The nominal run of a discrete-time system

The state sequence `simulate(linsysDT, params)` returns when `w = 0` and `v = 0`, as
`priv_conform_unifyTrajectories` [1] calls it to get the nominal solution a test case's
output is compared with: `x(k+1) = A x(k) + B u(k) + c`.

## Inputs
* `sys` – system
* `x0` – initial state
* `u` – inputs

## Output
* the nominal state after each number of steps

## References

* [1] `contDynamics/@linearSysDT/private/priv_conform_unifyTrajectories.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x(0) = x0`, `x(k+1) = A x(k) + B u(k) + c`. -/
noncomputable def LinearSysDT.nominalState (sys : LinearSysDT ℝ n) (x0 : Vec ℝ n)
    (u : ℕ → Vec ℝ sys.m) : ℕ → Vec ℝ n
  | 0 => x0
  | k + 1 => sys.A *ᵥ LinearSysDT.nominalState sys x0 u k + sys.B *ᵥ u k + sys.c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
