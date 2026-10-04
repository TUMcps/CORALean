import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# The nominal run of a discrete-time system

The state sequence `simulate(linsysDT, params)` returns when `w = 0` and `v = 0`, as
`priv_conform_unifyTrajectories` [1] calls it to get the nominal solution a test case's
output is compared with: `x(k+1) = A x(k) + B u(k) + c`. The record keeps `A` only, so `B`,
`c` are arguments.

## References

* [1] `contDynamics/@linearSysDT/private/priv_conform_unifyTrajectories.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x(0) = x0`, `x(k+1) = A x(k) + B u(k) + c`. -/
noncomputable def LinearSysDT.nominalState (sys : LinearSysDT ℝ n) (B : Mat ℝ n m) (c : Vec ℝ n)
    (x0 : Vec ℝ n) (u : ℕ → Vec ℝ m) : ℕ → Vec ℝ n
  | 0 => x0
  | k + 1 => sys.A *ᵥ LinearSysDT.nominalState sys B c x0 u k + B *ᵥ u k + c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
