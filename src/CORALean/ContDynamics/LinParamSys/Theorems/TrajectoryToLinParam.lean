import CORALean.ContDynamics.LinParamSys.Theorems.ToLinParam

/-!
# A `LinearSys` trajectory is a `toLinParam` trajectory at the constant matrix

`LinearSys.Trajectory.flow` already runs against the fixed matrix `toRealMat
sys.A`, so it is a `ConstTrajectory` there directly; `param` is
`OfPoint.mem_ofPoint`. The converse — a `toLinParam` `ConstTrajectory` is a
`LinearSys.Trajectory` — needs the matrix set to denote *only* `toRealMat
sys.A`, which `OfPoint` alone does not give: `mem_ofPoint` says the point is
in the set, never that the set is only the point. Not stated.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [OfPoint (𝕄 n n) (Mat ℝ n n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.toLinParam {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) :
    (sys.toLinParam (𝕄 := 𝕄)).ConstTrajectory T R₀ U x u (toRealMat sys.A) where
  init := traj.init
  input := traj.input
  param := OfPoint.mem_ofPoint (toRealMat sys.A)
  meas := traj.meas
  cont := traj.cont
  flow := traj.flow

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
