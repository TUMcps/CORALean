import CORALean.ContDynamics.NonlinearSys.Theorems.LinearEmbedding

/-!
# A linear system's trajectories are its embedding's

Split out of `LinearEmbedding.lean` (issue #62): the guarantee about
`nonlinearSys`, kept apart now that a file holds one public declaration.

The two `Trajectory` predicates agree by `rfl`: same time domain, same
initial condition, same input condition, same derivative.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

theorem LinearSys.trajectory_iff_nonlinearSys (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (R₀ U : S n) (x u : ℝ → Vec ℝ n) :
    sys.Trajectory T R₀ U x u ↔ sys.nonlinearSys.Trajectory T R₀ U x u :=
  ⟨fun h => ⟨h.init, h.input, h.flow⟩, fun h => ⟨h.init, h.input, h.flow⟩⟩

end CORALean.Real
