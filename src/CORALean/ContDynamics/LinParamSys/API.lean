import CORALean.ContDynamics.LinParamSys.Definitions.API
import CORALean.ContDynamics.LinParamSys.Instances
import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinParamSys.Operations.API
import CORALean.ContDynamics.LinParamSys.Theorems.API

/-!
# Continuous-time linear systems with a set-valued system matrix, collected

The system and its two trajectory predicates, `Trajectory` and
`ConstTrajectory`, in `LinParamSys`; one step of the flow and of the input, at
every matrix the set holds, in `Operations`; the guarantees relating the two
readings and enclosing a run in `Theorems`.

Reachability is at `ℐ`, because the exponential of a matrix set and its
correction matrix are interval matrices, and over windows: the first window's
sets, carried to window `k` by the box `t_k • sys.A`'s exponential. Both halves
hold at every time of a window, the input's through the frozen member's own
`inputReach`, which `inputReach_mono` grows once the input set holds the origin.

`'varParam'` is enclosed too, by freezing one member and paying the parameter
mismatch into the input set — not by CORA's `expmIndMixed`, whose soundness
needs a Peano-Baker expansion the tree has not got.

`Instances` is `Reach`'s, at `ℐ`: `LinearSys`'s windowed instances,
`ConstTrajectory` in place of `Trajectory`.
-/
