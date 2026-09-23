import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
import CORALean.ContDynamics.NonlinearSys.Definitions.PolyAbstractionError
import CORALean.ContDynamics.NonlinearSys.Definitions.LinStep
import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrState
import CORALean.ContDynamics.NonlinearSys.Definitions.AdaptState
import CORALean.ContDynamics.NonlinearSys.Definitions.CentreAbstrState
import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReach
import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSet

/-!
# What `NonlinearSys` means beyond the system itself

`AbstractionError`/`PolyAbstractionError` are the certificates a linearization
is checked against; `LinStep` bundles one linearization with its certificate.
`AbstrState`/`AdaptState`/`CentreAbstrState`/`PolyReachState` (with
`PolyTaylor`/`PolyPost`) are what each reachability loop hands its next
iteration. `ReachSet` is the set the flow actually reaches.
-/
