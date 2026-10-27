module

public import CORALean.ContDynamics.NonlinearSys.Definitions.IsAbstractionError
public import CORALean.ContDynamics.NonlinearSys.Definitions.IsPolyAbstractionError
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinStep
public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrState
public import CORALean.ContDynamics.NonlinearSys.Definitions.AdaptState
public import CORALean.ContDynamics.NonlinearSys.Definitions.OptStep
public import CORALean.ContDynamics.NonlinearSys.Definitions.TunedStep
public import CORALean.ContDynamics.NonlinearSys.Definitions.CenterAbstrState
public import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReach
public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Definitions.RobustReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Definitions.RelinReachOptions
public import CORALean.ContDynamics.NonlinearSys.Definitions.RelinDeltaReachOptions
public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrReachOptions
public import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReachOptions
public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NonlinearSys.Definitions.WithSteps
public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatHessModel
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAlg
public import CORALean.ContDynamics.NonlinearSys.Definitions.AdmissibleLinError
public import CORALean.ContDynamics.NonlinearSys.Definitions.CancelRedundant
public import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffOps
public import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffState
public import CORALean.ContDynamics.NonlinearSys.Definitions.IsInnerMinkDiffCert
public import CORALean.ContDynamics.NonlinearSys.Definitions.IsInnerMinkDiffCorrectedCert
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachInnerOps
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachInnerState
public import CORALean.ContDynamics.NonlinearSys.Definitions.IsLinReachInnerCert

/-!
# What `NonlinearSys` means beyond the system itself

`IsAbstractionError`/`IsPolyAbstractionError` are the certificates a linearization
is checked against; `LinStep` bundles one linearization with its certificate.
`OptStep`/`TunedStep` are what `optDeltat` and the tuning of `Δt` return.
`AbstrState`/`AdaptState`/`CenterAbstrState`/`PolyReachState` (with
`PolyTaylor`/`PolyPost`) are what each reachability loop hands its next
iteration. `ReachSetExact` is the set the flow actually reaches, `RobustReachSetExact` the one
reached against every disturbance. `WithSteps` bundles the
system with a chain of `LinStep`s and checkable regions, and `ReachUnionExact` is
the set a `Reach` run encloses. `RelinReachOptions`,
`RelinDeltaReachOptions`, `AbstrReachOptions` and `PolyReachOptions` are CORA's
`options` for the algorithms of those names. `FloatModel` is what a float run evaluates in
place of `f`, and `FloatModel.Encloses` ties it to `f`; `FloatHessModel` adds the Hessian, and
`LinReachAlg` is CORA's `options.alg`.
-/
