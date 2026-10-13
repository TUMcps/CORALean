import CORALean.ContDynamics.NonlinearSysDT.Operations.Linearize
import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
import CORALean.ContDynamics.NonlinearSysDT.Operations.ReachUnion
import CORALean.ContDynamics.NonlinearSysDT.Operations.Simulate
import CORALean.ContDynamics.NonlinearSysDT.Operations.SimulateBoxFloat
import CORALean.ContDynamics.NonlinearSysDT.Operations.ComputeGO
import CORALean.ContDynamics.NonlinearSysDT.Operations.ComputeGOFloat
import CORALean.ContDynamics.NonlinearSysDT.Operations.RefState
import CORALean.ContDynamics.NonlinearSysDT.Operations.Identify
import CORALean.ContDynamics.NonlinearSysDT.Operations.IdentifyCandidate
import CORALean.ContDynamics.NonlinearSysDT.Operations.ObserveStepFloat
import CORALean.ContDynamics.NonlinearSysDT.Operations.ObserveStripBasedFloat
import CORALean.ContDynamics.NonlinearSysDT.Operations.ReachSpecCora

/-!
# What `NonlinearSysDT` computes

`Reach` runs `LinearSysDT.reach` one step per linearization, at `Linearize`'s
fresh linear system and `LinInput`'s widened input set. `ReachUnion` is its
steps as `Reach` runs them, `none` once a run-time region test fails.
`Simulate` samples one run directly against `sys.f`, no linearization needed.
`ObserveStripBasedFloat` is the strip-based observer of `executeObserver`, whose prediction is
`Reach`'s step (`ObserveStepFloat`).
-/
