module

public import CORALean.ContDynamics.NonlinParamSys.Operations.ToNonlinearSys

@[expose] public section

/-!
# The combined-input embedding's trajectories are the parametric system's

The mirror-image hypothesis of `TrajectoryToNonlinearSys.lean`: `hUP` reads the
two projections of a member of `construct W` back into `construct U` and
`construct P`, which is what lets `w ∘ Fin.castAdd q` and `w ∘ Fin.natAdd m`
serve as `u` and `p`. `sys.toNonlinearSys.f` unfolds to exactly that split, so
`flow` needs no rewriting.

## Inputs
* `sys` – parametric system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `P` – parameter set
* `W` – combined input set
* `x` – state trajectory
* `w` – combined input signal
* `y` – output signal

## Hypotheses
* `traj` – trajectory of the combined-input system
* `hUP` – both parts of a combined input lie in their sets

## Conclusion
* the run is a parametric trajectory with the input and parameter split
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m q : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.isTrajectory_of_toNonlinearSys {sys : NonlinParamSys n m q} {T : Set ℝ}
    {R₀ : S n} {U : S m} {P : S q} {W : S (m + q)} {x : ℝ → Vec ℝ n} {w : ℝ → Vec ℝ (m + q)}
    {y : ℝ → Vec ℝ sys.r} (traj : sys.toNonlinearSys.IsTrajectory T R₀ W x w y)
    (hUP : ∀ v ∈ construct W, v ∘ Fin.castAdd q ∈ construct U ∧ v ∘ Fin.natAdd m ∈ construct P) :
    sys.IsTrajectory T R₀ U P x (fun t => w t ∘ Fin.castAdd q) (fun t => w t ∘ Fin.natAdd m)
      y where
  init := traj.init
  input t ht := (hUP (w t) (traj.input t ht)).1
  param t ht := (hUP (w t) (traj.input t ht)).2
  meas := traj.meas
  integrable := traj.integrable
  cont := traj.cont
  flow t ht := traj.flow t ht
  output t ht := traj.output t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
