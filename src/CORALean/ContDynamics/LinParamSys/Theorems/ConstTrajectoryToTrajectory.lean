import CORALean.ContDynamics.LinParamSys.LinParamSys

/-!
# A constant-parameter trajectory is a time-varying one

CORA's `'constParam'` is a special case of `'varParam'`: witness the constant
function `fun _ => A`. The converse fails — a trajectory free to pick a fresh
`A t` at each instant need not settle on one matrix — and is not stated here,
having no counterexample constructed.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.constTrajectory_toTrajectory {sys : LinParamSys 𝕄 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n}
    (traj : sys.ConstTrajectory T R₀ U x u A) :
    sys.Trajectory T R₀ U x u (fun _ => A) where
  init := traj.init
  input := traj.input
  param _ _ := traj.param
  meas := traj.meas
  measParam := MeasureTheory.aestronglyMeasurable_const
  cont := traj.cont
  flow := traj.flow

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
