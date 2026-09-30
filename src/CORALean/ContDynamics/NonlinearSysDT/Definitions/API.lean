import CORALean.ContDynamics.NonlinearSysDT.Definitions.LinStep
import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachOptions
import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachParams
import CORALean.ContDynamics.NonlinearSysDT.Definitions.ReachUnionExact
import CORALean.ContDynamics.NonlinearSysDT.Definitions.WithSteps

/-!
# What `NonlinearSysDT` means beyond the system itself

`LinStep`: one linearization of `sys`, with the `AbstractionError` certificate
that makes it conservative wherever the state stays in `R`. `WithSteps` bundles
the system with a chain of them and checkable regions, `ReachParams` is what a
`Reach` run takes, and `ReachUnionExact` is the set it encloses.
-/
