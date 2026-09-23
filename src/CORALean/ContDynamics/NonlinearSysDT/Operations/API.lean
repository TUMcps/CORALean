import CORALean.ContDynamics.NonlinearSysDT.Operations.Linearize
import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
import CORALean.ContDynamics.NonlinearSysDT.Operations.Simulate

/-!
# What `NonlinearSysDT` computes

`Reach` runs `LinearSysDT.reach` one step per linearization, at `Linearize`'s
fresh linear system and `LinInput`'s widened input set. `Simulate` samples
one run directly against `sys.f`, no linearization needed.
-/
