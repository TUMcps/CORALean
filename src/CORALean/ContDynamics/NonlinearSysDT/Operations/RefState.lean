module

public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT

@[expose] public section

/-!
# The reference run of a discrete-time system

`x_ref(:,k+1) = nlnsysDT.mFile(x_ref(:,k), u_ref(:,k))` of `computeGO`, from `x_ref(:,1) = x0`.

## Inputs
* `sys` – system
* `x0` – initial point
* `u_ref` – reference input

## Output
* the reference states at each step
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The states reached from `x0` under the reference inputs `u_ref`. -/
def NonlinearSysDT.refState (sys : NonlinearSysDT n m) (x0 : Vec ℝ n) (u_ref : ℕ → Vec ℝ m) :
    ℕ → Vec ℝ n
  | 0 => x0
  | k + 1 => sys.f (sys.refState x0 u_ref k) (u_ref k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
