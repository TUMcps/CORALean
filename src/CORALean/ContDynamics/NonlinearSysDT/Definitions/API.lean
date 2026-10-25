module

public import CORALean.ContDynamics.NonlinearSysDT.Definitions.FloatModel
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.LinStep
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachOptions
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.WithSteps
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.GO
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.GOFloat
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.FloatJacModel
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.ConsistentSet
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.ExactUncertainSet

/-!
# What `NonlinearSysDT` means beyond the system itself

`LinStep`: one linearization of `sys`, with the `IsAbstractionError` certificate
that makes it conservative wherever the state stays in `R`. `WithSteps` bundles
the system with a chain of them and checkable regions, and `ReachUnionExact` is
the set a `Reach` run encloses; `ReachOptions` is CORA's `options` for it.
-/
