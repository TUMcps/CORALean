import CORALean.ContDynamics.LinParamSys.Definitions.WithInput
import CORALean.ContDynamics.LinearSys.Definitions.ReachParams

/-!
# The exact set `Reach LinParamSys.WithInput` is asked to enclose

Every state a `'constParam'` run on the horizon `[0, p.tFinal]` is at, at some
time of it: one matrix `A` of `sys.A` fixed over the whole run, the initial
state in a bare set `X`, the input in `sys.U` — `ConstTrajectory`, at the
representation `Set` itself. At `sys.U = {0}` it is
`LinParamSys.reachUnionExact`'s set.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state a constant-parameter run on `[0, p.tFinal]` from a bare initial
set `X`, under inputs in `sys.U`, is at, at some time of that horizon. -/
def LinParamSys.WithInput.reachUnionExact (sys : LinParamSys.WithInput S n)
    (p : LinearSys.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  {y | ∃ A : Mat ℝ n n, ∃ x u : ℝ → Vec ℝ n,
    sys.sys.ConstTrajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 p.tFinal) X
      (construct sys.U) x u A ∧ ∃ t ∈ Set.Icc (0 : ℝ) p.tFinal, x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
