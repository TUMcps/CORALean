module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# The linear system a linearization leaves behind

CORA's `nonlinearSys/private/linearize`, minus the derivative: the system is the matrix and
nothing else. Everything the field contributes beyond `A x` is collected in `linInput` instead,
so the two halves of a linearization are two definitions. `sys` is not an argument: `A` is
whatever matrix the certificate was issued for. `LinearSys ℝ`, not `LinearSys 𝕋`: the
certificate's `A` is real, and a float layer certifies against the real matrix its result reads as.

## Inputs
* `A` – state matrix

## Output
* the linear system with that matrix
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The linear system a linearization at any matrix `A` produces. -/
def NonlinearSys.linearize (A : Mat ℝ n n) : LinearSys ℝ n := LinearSys.canonical A

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
