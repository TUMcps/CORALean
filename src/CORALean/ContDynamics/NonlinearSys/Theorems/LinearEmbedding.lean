import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# A linear system is a nonlinear one

`ẋ = A x + u` is the field `f(x, u) = A x + u`. Here rather than in
`LinearSys`, so that deleting this directory leaves the linear development
standing — the conversion belongs to the more general representation. The
guarantee that trajectories agree is `TrajectoryIffNonlinearSys.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The field a linear system is. -/
def LinearSys.nonlinearSys (sys : LinearSys 𝕋 n) : NonlinearSys n n :=
  ⟨fun x u => toRealMat sys.A *ᵥ x + u⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
