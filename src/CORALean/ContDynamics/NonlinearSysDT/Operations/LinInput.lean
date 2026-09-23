import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
import CORALean.ContDynamics.NonlinearSysDT.Definitions.LinStep

/-!
# The input set one discrete linearization step has to be given

`LinStep.linInput` widens `U` by the step's own certificate, exactly as
`NonlinearSys`'s `linInput` does — stated over `f` itself, so it applies here
unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The input set this step's linear system has to be given. -/
def NonlinearSysDT.LinStep.linInput {sys : NonlinearSysDT n m} {U : S m}
    (step : sys.LinStep U) : S n :=
  CORALean.linInput sys.f step.A step.B step.xs step.us U step.L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
