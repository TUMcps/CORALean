module

public import CORALean.ContDynamics.NonlinearSysDT.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
public import CORALean.ContDynamics.NonlinearSysDT.Operations.ReachUnion
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Simulate
public import CORALean.ContDynamics.NonlinearSysDT.Operations.SimulateBoxFloat
public import CORALean.ContDynamics.NonlinearSysDT.Operations.ComputeGO
public import CORALean.ContDynamics.NonlinearSysDT.Operations.ComputeGOFloat
public import CORALean.ContDynamics.NonlinearSysDT.Operations.RefState
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Identify
public import CORALean.ContDynamics.NonlinearSysDT.Operations.IdentifyCandidate
public import CORALean.ContDynamics.NonlinearSysDT.Operations.ObserveStepFloat
public import CORALean.ContDynamics.NonlinearSysDT.Operations.ObserveStripBasedFloat

/-!
# What `NonlinearSysDT` computes

`Reach` runs `LinearSysDT.reach` one step per linearization, at `Linearize`'s
fresh linear system and `LinInput`'s widened input set. `ReachUnion` is its
steps as `Reach` runs them, `none` once a run-time region test fails.
`Simulate` samples one run directly against `sys.f`, no linearization needed.
`ObserveStripBasedFloat` is the strip-based observer of `executeObserver`, whose prediction is
`Reach`'s step (`ObserveStepFloat`).
-/
