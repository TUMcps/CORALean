import CORALean.ContDynamics.NonlinearSysDT.Definitions.FloatModel
import CORALean.ContDynamics.NonlinearSysDT.Definitions.LinStep
import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachOptions
import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachUnionExact
import CORALean.ContDynamics.NonlinearSysDT.Definitions.WithSteps
import CORALean.ContDynamics.NonlinearSysDT.Definitions.GO
import CORALean.ContDynamics.NonlinearSysDT.Definitions.GOFloat
import CORALean.ContDynamics.NonlinearSysDT.Definitions.FloatJacModel
import CORALean.ContDynamics.NonlinearSysDT.Definitions.ConsistentSet
import CORALean.ContDynamics.NonlinearSysDT.Definitions.ExactUncertainSet

/-!
# What `NonlinearSysDT` means beyond the system itself

`LinStep`: one linearization of `sys`, with the `AbstractionError` certificate
that makes it conservative wherever the state stays in `R`. `WithSteps` bundles
the system with a chain of them and checkable regions, and `ReachUnionExact` is
the set a `Reach` run encloses; `ReachOptions` is CORA's `options` for it.
-/
