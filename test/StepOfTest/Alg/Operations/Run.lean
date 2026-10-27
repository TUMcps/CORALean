module

public import CORALean.Global.StepOf

/-! An algorithm `run` with one step, `step_half`. -/

@[expose] public section

namespace StepOfTest

/-- Halves `n`. -/
@[step_of run] def step_half (n : Nat) : Nat := n / 2

/-- Halves `n` and adds one. -/
def run (n : Nat) : Nat := step_half n + 1

end StepOfTest
