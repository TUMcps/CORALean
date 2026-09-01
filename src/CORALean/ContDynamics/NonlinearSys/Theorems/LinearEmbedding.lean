import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# A linear system is a nonlinear one

`ẋ = A x + u` is the field `f(x, u) = A x + u`, and the two `Trajectory`
predicates then agree by `rfl`: same initial condition, same input condition,
same derivative.

Here rather than in `LinearSys`, so that deleting this directory leaves the
linear development standing — the conversion belongs to the more general
representation.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

/-- The field a linear system is. -/
def LinearSys.nonlinearSys (sys : LinearSys 𝕋 n) : NonlinearSys n n :=
  ⟨fun x u => toRealMat sys.A *ᵥ x + u⟩

theorem LinearSys.trajectory_iff_nonlinearSys (sys : LinearSys 𝕋 n) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) :
    sys.Trajectory R₀ U x u ↔ sys.nonlinearSys.Trajectory R₀ U x u :=
  ⟨fun h => ⟨h.init, h.input, h.flow⟩, fun h => ⟨h.init, h.input, h.flow⟩⟩

end CORALean.Real
