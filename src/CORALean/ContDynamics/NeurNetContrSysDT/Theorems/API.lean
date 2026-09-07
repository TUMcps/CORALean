import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.EqOfInit
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfOutput
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.NotHoldsOfSimulate
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.OutputOuter
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.SimulateMemReach
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.SimulateTrajectory
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.TrajectoryIterate

/-!
# What a network in the loop guarantees

`ReachOuter` is the composition of the two halves, `HoldsOfReach` what checking
a specification on it buys, and `TrajectoryIterate`/`EqOfInit` the reading of a
run that a determined input forces: an orbit, not a family, settled by where
it started.

`OutputOuter`/`HoldsOfOutput` are those two at an `OutputEq`, read at the
controller's own enclosure in place of a free input set — there is
none here, `map` already reading it off the state.

`SimulateTrajectory`/`SimulateMemReach` are `simulate` sampling one run and
landing inside `reach`, with two obligations rather than three: the controller
supplies the input, so nothing needs stating about it. `NotHoldsOfSimulate` is
the falsification corollary: one sampled run violating a specification settles
it, where an enclosure can only ever fail to prove safety.

No `reach_outer_on`: there is no `TrajectoryOn` here to hand it a bounded run
from, since a run is already the orbit of `map` from its start
(`TrajectoryIterate`) — nothing a horizon could leave unknown that `reach_outer`
does not already cover at every `k`.
-/
