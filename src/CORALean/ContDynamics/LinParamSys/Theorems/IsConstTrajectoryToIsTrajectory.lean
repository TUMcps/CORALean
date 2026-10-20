module

public import CORALean.ContDynamics.LinParamSys.LinParamSys

@[expose] public section

/-!
# A constant-parameter trajectory is a time-varying one

CORA's `'constParam'` is a special case of `'varParam'`: witness the constant
function `fun _ => A`. The converse fails — a trajectory free to pick a fresh
`A t` at each instant need not settle on one matrix — and is not stated here,
having no counterexample constructed.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – input signal
* `A` – system matrix member

## Hypotheses
* `traj` – constant-parameter trajectory

## Conclusion
* the constant matrix function gives a time-varying trajectory
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.isConstTrajectory_toIsTrajectory {sys : LinParamSys 𝕄 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n}
    (traj : sys.IsCanonicalConstTrajectory T R₀ U x u A) :
    sys.IsCanonicalTrajectory T R₀ U x u (fun _ => A) where
  init := traj.init
  input := traj.input
  param _ _ := traj.param
  meas := traj.meas
  measParam := MeasureTheory.aestronglyMeasurable_const
  cont := traj.cont
  flow := traj.flow

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
