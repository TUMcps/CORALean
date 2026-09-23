import CORALean.ContDynamics.NonlinearSys.Definitions.LinStep
import CORALean.ContDynamics.NonlinearSys.Operations.LinInput

/-!
# The input set one re-linearization step has to be given

`LinStep.linInput`: `Δt` and the order bound `o` are uniform and stay
arguments of `relinReach`; varying them per step is adaptive tuning, a
separate method. The discrete input set is what a step is *run* with rather
than what the linearization *is*.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
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
def NonlinearSys.LinStep.linInput {sys : NonlinearSys n m} {U : S m}
    (step : sys.LinStep U) : S n :=
  CORALean.linInput sys.f step.A step.B step.xs step.us U step.L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
