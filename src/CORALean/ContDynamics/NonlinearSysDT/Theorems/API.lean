module

public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ConfinementOfSubset
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ConfinementOfSubsetOn
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfCheck
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfReach
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfReachOfSubset
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.LinStepLinInputOuter
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.NotHoldsOfSimulate
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOfSubset
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOn
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateMemReach
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateIsTrajectory
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.SimulateMemSimulateBoxFloat
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ComputeGOState
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ComputeGOOutput
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ComputeGOFloatOuter
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.IdentifyCandidateFit
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.IdentifyLeCandidate
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ObserveStepFloatOuter
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ObserveStripBasedFloatOuter
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ConsistentSetInterSubsetStrip
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ConsistentSetSubsetIInter
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ExactUncertainSetSubset
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ExactUncertainSetSucc

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

`ObserveStepFloatOuter`/`ObserveStripBasedFloatOuter`: the observer's set holds the true state.

No `output_outer`/`holds_of_output`: `OutputEq` is the *linear* map `C x + D u`,
and a nonlinear `g` needs its own enclosure — the same problem as enclosing
`f`, which `NonlinearSys` already declines for the same reason.
-/
