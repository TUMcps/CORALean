module

public import CORALean.NN.Operations.AtSchedule
public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# Propagating at a schedule

`atSchedule` produces an ordinary `NeuralNetwork`, so propagating at a schedule
is `enclose` there and nothing new — every guarantee `enclose` already has
transfers to every schedule for free.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Propagating at a schedule, which is `enclose` and nothing new. -/
def RefinableNetwork.encloseAt (rn : RefinableNetwork S n m) (sch : Schedule) (X : S n) : S m :=
  (rn.atSchedule sch).enclose X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
