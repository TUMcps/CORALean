import CORALean.ContDynamics.NonlinearSysDT.Theorems.ConfinementOfSubset
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ConfinementOfSubsetOn
import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfCheck
import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfReachOfSubset
import CORALean.ContDynamics.NonlinearSysDT.Theorems.LinStepLinInputOuter
import CORALean.ContDynamics.NonlinearSysDT.Theorems.NotHoldsOfSimulate
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOfSubset
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOn
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachUnionOuter
import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateMemReach
import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateTrajectory

/-!
# What `NonlinearSysDT` guarantees

That `reach` contains every trajectory, by induction on the step count — the
discrete counterpart of `NonlinearSys.relinReach_outer`, without the shifting
that continuous time forces there. `HoldsOfReach`/`HoldsOfReachOfSubset` are
that at a specification, threading the linearization `steps` and its
confinement through rather than hiding them; `NotHoldsOfSimulate` is the
falsification corollary, at `simulate`'s own confinement.

`SimulateTrajectory`/`SimulateMemReach` are `simulate` sampling one run and
landing inside `reach`, at whatever confinement `reach_outer` itself needs.

`ConfinementOfSubset`/`ReachOuterOfSubset` discharge that hypothesis from the computed sets: a
caller checks `hsub` instead of assuming confinement of the trajectory. Sound at every `steps` that
passes; CORA's enlarge-and-retry search for one that does is not implemented here.
`ConfinementOfSubsetOn` is the same for a run known up to a bound, and `ReachUnionOuter` spends it
on the tests `reachUnion` runs.

No `output_outer`/`holds_of_output`: `OutputEq` is the *linear* map `C x + D u`,
and a nonlinear `g` needs its own enclosure — the same problem as enclosing
`f`, which `NonlinearSys` already declines for the same reason.
-/
