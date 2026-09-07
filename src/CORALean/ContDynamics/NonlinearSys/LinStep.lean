import CORALean.ContDynamics.NonlinearSys.AbstractionError
import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.NonlinearSys.Operations.LinInput

/-!
# One step of the re-linearization loop

A single linearization is `AbstractionError` together with the matrices and the
expansion point it was issued for. Bundling them is what makes a *sequence* of
linearizations sayable: seven parallel families indexed by the step count is not
a statement anyone can read, and the certificate has to travel with the data it
certifies or the wrong `L` reaches the wrong `A`.

A chain of steps is a function `ℕ → LinStep`: `relinReach` recurses on the step
index and looks nothing up, the composition theorem is `Nat.rec` with one
hypothesis family `∀ i < N` per obligation, and a chain longer than the horizon
costs nothing. Not an inductive chain as `HybridAutomaton.Run` is: a hybrid run is
a datum of the *system*, a chain of linearizations one of the *analysis*, and
inductive would put the enclosures inside the proof.

`Δt` and the order bound `o` are uniform and stay arguments of `relinReach`;
varying them per step is adaptive tuning, a separate method. The discrete input
set is what a step is *run* with rather than what the linearization *is*.
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


-- ========================================  MAIN TYPE  ========================================= --

/-- One linearization of `sys`, with the certificate that makes it conservative
wherever the state stays in `R`. -/
structure NonlinearSys.LinStep (sys : NonlinearSys n m) (U : S m) where
  A : Mat ℝ n n
  B : Mat ℝ n m
  xs : Vec ℝ n
  us : Vec ℝ m
  R : Set (Vec ℝ n)
  L : S n
  cert : AbstractionError sys.f A B xs us R (construct U) L

/-- The input set this step's linear system has to be given. -/
def NonlinearSys.LinStep.linInput {sys : NonlinearSys n m} {U : S m}
    (step : sys.LinStep U) : S n :=
  CORALean.linInput sys.f step.A step.B step.xs step.us U step.L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
