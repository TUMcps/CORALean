module

public import CORALean.ContDynamics.LinParamSys.Operations.ToLinParam

@[expose] public section

/-!
# A `LinearSys` trajectory is a `toLinParam` trajectory at the constant matrix

`LinearSys.CanonicalTrajectory.flow` already runs against the fixed matrix `toRealMat
sys.A`, so it is a `ConstTrajectory` there directly; `param` is
`OfPoint.mem_ofPoint`. The converse — a `toLinParam` `ConstTrajectory` is a
`LinearSys.CanonicalTrajectory` — needs the matrix set to denote *only* `toRealMat
sys.A`, which `OfPoint` alone does not give: `mem_ofPoint` says the point is
in the set, never that the set is only the point. Not stated.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable [∀ m n, OfPoint (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.CanonicalTrajectory.toLinParam {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.CanonicalTrajectory T R₀ U x u) :
    (sys.toLinParam (𝕄 := 𝕄)).CanonicalConstTrajectory T R₀ U x u (toRealMat sys.A) where
  init := traj.init
  input := traj.input
  param := OfPoint.mem_ofPoint (toRealMat sys.A)
  meas := traj.meas
  cont := traj.cont
  flow := traj.flow

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
