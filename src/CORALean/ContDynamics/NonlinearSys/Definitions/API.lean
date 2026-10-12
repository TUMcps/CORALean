import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
import CORALean.ContDynamics.NonlinearSys.Definitions.PolyAbstractionError
import CORALean.ContDynamics.NonlinearSys.Definitions.LinStep
import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrState
import CORALean.ContDynamics.NonlinearSys.Definitions.AdaptState
import CORALean.ContDynamics.NonlinearSys.Definitions.CentreAbstrState
import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReach
import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSet
import CORALean.ContDynamics.NonlinearSys.Definitions.RobustReachSet
import CORALean.ContDynamics.NonlinearSys.Definitions.RelinReachOptions
import CORALean.ContDynamics.NonlinearSys.Definitions.RelinDeltaReachOptions
import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrReachOptions
import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReachOptions
import CORALean.ContDynamics.NonlinearSys.Definitions.ReachUnionExact
import CORALean.ContDynamics.NonlinearSys.Definitions.WithSteps
import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
import CORALean.ContDynamics.NonlinearSys.Definitions.FloatHessModel
import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAlg
import CORALean.ContDynamics.NonlinearSys.Definitions.AdmissibleLinError
import CORALean.ContDynamics.NonlinearSys.Definitions.CancelRedundant
import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffOps
import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffState
import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffCert

/-!
# What `NonlinearSys` means beyond the system itself

`AbstractionError`/`PolyAbstractionError` are the certificates a linearization
is checked against; `LinStep` bundles one linearization with its certificate.
`AbstrState`/`AdaptState`/`CentreAbstrState`/`PolyReachState` (with
`PolyTaylor`/`PolyPost`) are what each reachability loop hands its next
iteration. `ReachSet` is the set the flow actually reaches, `RobustReachSet` the one reached
against every disturbance. `WithSteps` bundles the
system with a chain of `LinStep`s and checkable regions, and `ReachUnionExact` is
the set a `Reach` run encloses. `RelinReachOptions`,
`RelinDeltaReachOptions`, `AbstrReachOptions` and `PolyReachOptions` are CORA's
`options` for the algorithms of those names. `FloatModel` is what a float run evaluates in
place of `f`, and `FloatModel.Encloses` ties it to `f`; `FloatHessModel` adds the Hessian, and
`LinReachAlg` is CORA's `options.alg`.
-/
