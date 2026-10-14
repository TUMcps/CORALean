module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# A constant-parameter run is a run of the system at the matrix it fixed

The direction `TrajectoryToLinParam` does not give: there a `LinearSys` becomes
a `LinParamSys` at the point its matrix denotes, here a `ConstTrajectory`
becomes the `LinearSys.CanonicalTrajectory` of the one matrix it holds fixed. The
matrix set is dropped, `param` with it, which is why nothing comes back the
other way without knowing the set is that point.

This is what lets the closed form — `variation_of_constants` and everything
resting on it — be used at `'constParam'` without being restated.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.CanonicalConstTrajectory.toLinearSys {sys : LinParamSys 𝕄 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n}
    (traj : sys.CanonicalConstTrajectory T R₀ U x u A) :
    (LinearSys.canonical A : LinearSys ℝ n).CanonicalTrajectory T R₀ U x u where
  init := traj.init
  input := traj.input
  meas := traj.meas
  cont := traj.cont
  flow := fun t ht => by simpa only [Scalar.toRealMat_real] using traj.flow t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
