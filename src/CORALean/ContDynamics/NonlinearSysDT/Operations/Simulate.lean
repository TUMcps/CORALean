module

public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT

@[expose] public section

/-!
# One sampled run of a discrete nonlinear system

`simulate` samples one run directly against `sys.f`, no linearization needed:
a point computation carrying none of `reach`'s set instances.
-/

-- Authors:       Claude Sonnet 5
-- Written:       04-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One sampled run of the dynamics from `x₀` under input signal `u` — a point
computation, none of `reach`'s set instances needed. -/
def NonlinearSysDT.simulate (sys : NonlinearSysDT n m) (x₀ : Vec ℝ n) (u : ℕ → Vec ℝ m) :
    ℕ → Vec ℝ n
  | 0 => x₀
  | k + 1 => sys.f (sys.simulate x₀ u k) (u k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
