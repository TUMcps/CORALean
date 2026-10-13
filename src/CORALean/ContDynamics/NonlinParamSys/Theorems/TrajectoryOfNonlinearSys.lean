import CORALean.ContDynamics.NonlinParamSys.Theorems.ToNonlinearSys

/-!
# The combined-input embedding's trajectories are the parametric system's

The mirror-image hypothesis of `TrajectoryToNonlinearSys.lean`: `hUP` reads the
two projections of a member of `construct W` back into `construct U` and
`construct P`, which is what lets `w ∘ Fin.castAdd q` and `w ∘ Fin.natAdd m`
serve as `u` and `p`. `sys.toNonlinearSys.f` unfolds to exactly that split, so
`flow` needs no rewriting.
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

theorem NonlinParamSys.trajectory_of_toNonlinearSys {sys : NonlinParamSys n m q} {T : Set ℝ}
    {R₀ : S n} {U : S m} {P : S q} {W : S (m + q)} {x : ℝ → Vec ℝ n} {w : ℝ → Vec ℝ (m + q)}
    (traj : sys.toNonlinearSys.Trajectory T R₀ W x w)
    (hUP : ∀ v ∈ construct W, v ∘ Fin.castAdd q ∈ construct U ∧ v ∘ Fin.natAdd m ∈ construct P) :
    sys.Trajectory T R₀ U P x (fun t => w t ∘ Fin.castAdd q) (fun t => w t ∘ Fin.natAdd m) where
  init := traj.init
  input t ht := (hUP (w t) (traj.input t ht)).1
  param t ht := (hUP (w t) (traj.input t ht)).2
  flow t ht := traj.flow t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
