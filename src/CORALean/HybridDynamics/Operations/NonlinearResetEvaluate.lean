module

public import CORALean.HybridDynamics.Definitions.NonlinearReset

@[expose] public section

/-!
# `NonlinearReset.evaluate`

CORA's `nonlinearReset/evaluate` at numeric arguments: `x_ = nonlinReset.f(x, u)`. At a set it is a
Taylor enclosure with a Lagrange remainder, which is not here.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.evaluate (r : NonlinearReset n m p) (x : Vec ℝ n) (u : Vec ℝ m) : Vec ℝ p :=
  r.f x u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
