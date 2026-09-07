import CORALean.NN.Operations.AtSchedule
import CORALean.NN.Operations.Enclose

/-!
# Propagating at a schedule

`atSchedule` produces an ordinary `NeuralNetwork`, so propagating at a schedule
is `enclose` there and nothing new — every guarantee `enclose` already has
transfers to every schedule for free.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Propagating at a schedule, which is `enclose` and nothing new. -/
def RefinableNetwork.encloseAt (rn : RefinableNetwork S n m) (sch : Schedule) (X : S n) : S m :=
  (rn.atSchedule sch).enclose X

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
