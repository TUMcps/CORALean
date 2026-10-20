module

public import CORALean.ContDynamics.NonlinDASys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NonlinDASys.Theorems.IsTrajectoryOfNonlinearSys
public import CORALean.ContDynamics.NonlinDASys.Theorems.IsTrajectoryToNonlinearSys
public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachUnionExact

@[expose] public section

/-!
# The reachable states are the reduced system's, exactly

`reachUnionExact` of the differential-algebraic system is `reachUnionExact` of the bundled
ordinary system, as sets: a trajectory of one is a trajectory of the other
(`TrajectoryToNonlinearSys`, `TrajectoryOfNonlinearSys`), at the same `x`.

## Inputs
* `sys` – system with steps
* `tFinal` – horizon
* `X` – initial set

## Hypotheses
* none

## Conclusion
* the reachable states of the DAE and of its reduced system are equal
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]
variable {m p n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.WithSteps.reachUnionExact_eq (sys : NonlinDASys.WithSteps S Rg m p n)
    (tFinal : ℝ) (X : Set (Vec ℝ n)) : -- --- CONCL ---
    sys.reachUnionExact tFinal X = sys.ode.reachUnionExact tFinal X := by -- --- PROOF ---
  ext z
  simp only [NonlinDASys.WithSteps.reachUnionExact, NonlinearSys.WithSteps.reachUnionExact,
    NonlinearSys.reachSetExact, Set.mem_iUnion, Set.mem_setOf_eq]
  rw [sys.ode_sys]
  -- the outputs are read off the runs, the same on the horizon
  constructor
  · rintro ⟨t, ht, x, y, u, traj, rfl⟩
    exact ⟨t, ht, x, u, { traj.toNonlinearSys sys.red with output := fun _ _ => rfl }, rfl⟩
  · rintro ⟨t, ht, x, u, traj, rfl⟩
    exact ⟨t, ht, x, _, u, { traj.toNonlinDASys sys.red with output := fun _ _ => rfl }, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
