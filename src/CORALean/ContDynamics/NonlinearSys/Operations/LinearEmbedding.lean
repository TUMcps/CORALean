module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# A linear system is a nonlinear one

`ẋ = A x + u` is the field `f(x, u) = A x + u`. Here rather than in
`LinearSys`, so that deleting this directory leaves the linear development
standing — the conversion belongs to the more general representation. The
guarantee that trajectories agree is `ClassicalTrajectoryIffNonlinearSys.lean`.

## Inputs
* `sys` – linear system

## Output
* the linear system as a nonlinear one
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The field a linear system is. -/
def LinearSys.nonlinearSys (sys : LinearSys 𝕋 n) : NonlinearSys n n :=
  ⟨fun x u => toRealMat sys.A *ᵥ x + u, n, fun x _ => x⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
