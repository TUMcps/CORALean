module

public import CORALean.Global.ExactScalar
public import CORALean.HybridDynamics.Parallel.Definitions.Lifting
public import CORALean.HybridDynamics.Parallel.Definitions.SelfBindFree
public import CORALean.HybridDynamics.Parallel.Definitions.ReachSet
public import CORALean.Global.ExactAdd
public import CORALean.HybridDynamics.Parallel.Definitions.FlowLaw
public import CORALean.HybridDynamics.Parallel.Definitions.GlobalsDistinct
public import CORALean.HybridDynamics.Parallel.Definitions.InputsGlobalOnly
public import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact
public import CORALean.HybridDynamics.Parallel.Definitions.SyncLabels
public import CORALean.HybridDynamics.Parallel.Definitions.SyncLifting
public import CORALean.HybridDynamics.Parallel.Definitions.SyncRun
public import CORALean.HybridDynamics.Parallel.Definitions.OutputSource

/-!
# What a parallel hybrid automaton means

`ExactScalar` (`Global/ExactScalar`) is the exact `0` and `1` assembling a matrix out of the
components' asks of the scalar, `SelfBindFree` where that assembly is `A + B * C`, and `Lifting`
what lifting their sets into the product's space owes, a structure the caller fills. `ReachSet`
names what a `Run` quantifies over. `ExactAdd` is the exact sum that closes `SelfBindFree` at `ℝ`,
and `FlowLaw` what a product's matrix must do to a stack for the run theorems. `LiftingExact`,
`GlobalsDistinct` and `InputsGlobalOnly` are the conditions of the converse of `Run.toProduct`.
`SyncLabels`, `SyncLifting` and `SyncRun` are synchronization labels, their lifting and run
semantics.
-/
