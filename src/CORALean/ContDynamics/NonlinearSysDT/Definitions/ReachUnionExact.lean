import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachParams
import CORALean.ContDynamics.NonlinearSysDT.Definitions.WithSteps

/-!
# Every state a discrete nonlinear run reaches within the horizon

`Reach.reachExact` at `NonlinearSysDT.WithSteps`: every state some run is at,
at a step `k ≤ K`, from a bare initial set under inputs in `U`. A run need be
known only for its first `K` steps, `TrajectoryOn`, so no input is asked for
past the horizon. The bare set is the representation `Set` itself, which
`TrajectoryOn` accepts as it accepts any other. Nothing here mentions the
linearizations: they are how `reach` encloses this set, not part of it.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state a run known for `p.K` steps is at, at a step `k ≤ p.K`, from a
bare initial set `X` under inputs in `sys.U`. -/
def NonlinearSysDT.WithSteps.reachUnionExact (sys : NonlinearSysDT.WithSteps S Rg m n)
    (p : NonlinearSysDT.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ k ≤ p.K, {y | ∃ (x : ℕ → Vec ℝ n) (u : ℕ → Vec ℝ m),
    sys.sys.TrajectoryOn (S := fun k => Set (Vec ℝ k)) X (construct sys.U) p.K x u ∧ x k = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
