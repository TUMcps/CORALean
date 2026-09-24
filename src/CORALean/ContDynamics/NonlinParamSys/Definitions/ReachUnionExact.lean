import CORALean.ContDynamics.NonlinParamSys.Definitions.WithSteps
import CORALean.ContDynamics.NonlinearSys.Definitions.ReachParams

/-!
# Every state a constant-parameter run reaches within the horizon

`Reach.reachExact` at `NonlinParamSys.WithSteps`: every state some
`ConstTrajectory` of `sys` on `[0, NΔt]` is at, at some time of that horizon,
from a bare initial set under inputs in `aug.U` and one parameter in `P` for
the whole run. The uncertain-but-constant reading is the one the augmented
system encloses; a time-varying parameter, `Trajectory`, is not enclosed, its
augmented state not having zero derivative. Nothing here mentions the
augmentation or the linearizations: they are how `reach` encloses this set.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]
variable {m q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state a constant-parameter run on `[0, p.N * p.Δt]` from a bare initial
set `X`, under inputs in `aug.U` and a parameter in `P`, is at within that horizon. -/
def NonlinParamSys.WithSteps.reachUnionExact (sys : NonlinParamSys.WithSteps S Rg m q n)
    (p : NonlinearSys.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ t ∈ Set.Icc 0 ((p.N : ℝ) * p.Δt), {y | ∃ (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m)
    (π : Vec ℝ q), sys.sys.ConstTrajectory (S := fun k => Set (Vec ℝ k))
      (Set.Icc 0 ((p.N : ℝ) * p.Δt)) X (construct sys.aug.U) (construct sys.P) x u π ∧ x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
