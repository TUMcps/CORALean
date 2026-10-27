module

public import StepOfTest.Alg.Operations.Run

/-! A second algorithm `runFast`, whose name contains `Run`, with its own step. -/

@[expose] public section

namespace StepOfTest

/-- Quarters `n`. -/
@[step_of runFast] def step_quarter (n : Nat) : Nat := n / 4

/-- Quarters `n` and runs `run`. -/
def runFast (n : Nat) : Nat := run (step_quarter n)

end StepOfTest
