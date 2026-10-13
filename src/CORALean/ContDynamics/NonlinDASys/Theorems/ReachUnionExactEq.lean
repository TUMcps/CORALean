module

public import CORALean.ContDynamics.NonlinDASys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryOfNonlinearSys
public import CORALean.ContDynamics.NonlinDASys.Theorems.TrajectoryToNonlinearSys
public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachUnionExact

@[expose] public section

/-!
# The reachable states are the reduced system's, exactly

`reachUnionExact` of the differential-algebraic system is `reachUnionExact` of the bundled
ordinary system, as sets: a trajectory of one is a trajectory of the other
(`TrajectoryToNonlinearSys`, `TrajectoryOfNonlinearSys`), at the same `x`.
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
    (tFinal : ℝ) (X : Set (Vec ℝ n)) :
    sys.reachUnionExact tFinal X = sys.ode.reachUnionExact tFinal X := by -- --- PROOF ---
  ext z
  simp only [NonlinDASys.WithSteps.reachUnionExact, NonlinearSys.WithSteps.reachUnionExact,
    NonlinearSys.reachSet, Set.mem_iUnion, Set.mem_setOf_eq, sys.ode_sys]
  constructor
  · rintro ⟨t, ht, x, y, u, traj, rfl⟩
    exact ⟨t, ht, x, u, traj.toNonlinearSys sys.red, rfl⟩
  · rintro ⟨t, ht, x, u, traj, rfl⟩
    exact ⟨t, ht, x, _, u, traj.toNonlinDASys sys.red, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
