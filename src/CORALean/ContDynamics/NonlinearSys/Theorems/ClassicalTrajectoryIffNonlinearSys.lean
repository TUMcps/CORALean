module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinearEmbedding
public import CORALean.ContDynamics.LinearSys.Definitions.CanonicalClassicalTrajectory

@[expose] public section

/-!
# A linear system's classical runs are its embedding's

Split out of `LinearEmbedding.lean` (issue #62): the guarantee about
`nonlinearSys`, kept apart now that a file holds one public declaration.

`CanonicalClassicalTrajectory` and `NonlinearSys.CanonicalTrajectory` agree by `rfl`: same time
domain, same initial condition, same input condition, same derivative. Through
`CanonicalClassicalTrajectory.trajectory`, every such run is a `LinearSys.CanonicalTrajectory`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.classicalTrajectory_iff_nonlinearSys (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (R₀ U : S n) (x u : ℝ → Vec ℝ n) :
    sys.CanonicalClassicalTrajectory T R₀ U x u ↔ sys.nonlinearSys.Trajectory T R₀ U x u :=
  ⟨fun h => ⟨h.init, h.input, h.flow⟩, fun h => ⟨h.init, h.input, h.flow⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
