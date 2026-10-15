module

public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.EqOfInit
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfCheck
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfOutput
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfReach
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.NotHoldsOfSimulate
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.OutputOuter
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachSetOuter
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachSetSubsetReach
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.Real.API
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.SimulateMemReach
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.SimulateMemSimulateBoxFloat
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.SimulateTrajectory
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.TrajectoryIterate
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.TrajectoryLinear
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.TrajectoryOfMap

/-!
# What a network in the loop guarantees

`ReachOuter` is the composition of the two halves, `HoldsOfReach` what checking
a specification on it buys, and `TrajectoryLinear`/`TrajectoryOfMap`/`TrajectoryIterate`/
`EqOfInit` the reading of a run at a linear plant that a determined input forces: an orbit of
`map`, settled by where it started.

`ReachSetOuter`/`ReachSetSubsetReach` restate `ReachOuter` on the reachable
set; `Real/` bounds its generator count at `𝒵`, `ReachOrderLe` only holding at ℝ.

`OutputOuter`/`HoldsOfOutput` are those two at an `OutputEq`, read at the
controller's own enclosure in place of a free input set — none here, `map` already reading it off.

`SimulateTrajectory`/`SimulateMemReach` are `simulate` sampling one run and
landing inside `reach`, with two obligations rather than three: the controller
supplies the input, so nothing needs stating about it. `NotHoldsOfSimulate` is
the falsification corollary: one sampled run violating a specification settles
it, where an enclosure can only ever fail to prove safety.

No `reach_outer_on`: there is no `TrajectoryOn` here to hand it a bounded run
from, since a run is already the orbit of `map` from its start
(`TrajectoryIterate`) — nothing a horizon leaves unknown that `reach_outer`
does not cover at every `k`. `ReachUnionOuter` is `Instances`' guarantee.
-/
