import CORALean.NN.Operations.AtSchedule
import CORALean.NN.Operations.Propagate

/-!
# Propagating at a schedule

`atSchedule` produces an ordinary `NeuralNetwork`, so propagating at a schedule
is `propagate` there and nothing new — every guarantee `propagate` already has
transfers to every schedule for free.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

/-- Propagating at a schedule, which is `propagate` and nothing new. -/
def RefinableNetwork.propagateAt (rn : RefinableNetwork S n m) (sch : Schedule) (X : S n) : S m :=
  (rn.atSchedule sch).propagate X

end CORALean.Real
