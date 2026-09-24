import CORALean.ContDynamics.LinParamSys.Definitions.WithInputSplit
import CORALean.ContDynamics.LinearSys.Definitions.ReachParams

/-!
# The exact set `Reach LinParamSys.WithInputSplit` is asked to enclose

`LinParamSys.WithInput.reachUnionExact`'s set, with the input set anywhere:
every state a `'constParam'` run on `[0, p.tFinal]` is at, at some time of it,
one matrix `A` of `sys.A` fixed over the run, from a bare initial set, under
inputs in `sys.U`. The split of `U` and the windows are how `reach` encloses
this set, not part of it.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state a constant-parameter run on `[0, p.tFinal]` from a bare initial
set `X`, under inputs in `sys.U` wherever it sits, is at, at some time. -/
def LinParamSys.WithInputSplit.reachUnionExact (sys : LinParamSys.WithInputSplit S n)
    (p : LinearSys.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  {y | ∃ A : Mat ℝ n n, ∃ x u : ℝ → Vec ℝ n,
    sys.sys.ConstTrajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 p.tFinal) X
      (construct sys.U) x u A ∧ ∃ t ∈ Set.Icc (0 : ℝ) p.tFinal, x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
