module

public import CORALean.ContDynamics.LinParamSys.Operations.ToLinParam

@[expose] public section

/-!
# A `LinearSys` trajectory is a `toLinParam` trajectory at the constant matrix

`LinearSys.IsCanonicalTrajectory.flow` already runs against the fixed matrix `toRealMat
sys.A`, so it is a `IsConstTrajectory` there directly; `param` is
`OfPoint.mem_ofPoint`. The converse — a `toLinParam` `IsConstTrajectory` is a
`LinearSys.IsCanonicalTrajectory` — needs the matrix set to denote *only* `toRealMat
sys.A`, which `OfPoint` alone does not give: `mem_ofPoint` says the point is
in the set, never that the set is only the point. Not stated.

## Inputs
* `sys` – linear system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – input signal

## Hypotheses
* `traj` – linear-system trajectory

## Conclusion
* the trajectory is a constant-parameter trajectory at the system's matrix
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

theorem LinearSys.IsCanonicalTrajectory.toLinParam {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory T R₀ U x u) :
    (sys.toLinParam (𝕄 := 𝕄)).IsCanonicalConstTrajectory T R₀ U x u (toRealMat sys.A) where
  init := traj.init
  input := traj.input
  param := OfPoint.mem_ofPoint (toRealMat sys.A)
  meas := traj.meas
  cont := traj.cont
  flow := traj.flow

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
