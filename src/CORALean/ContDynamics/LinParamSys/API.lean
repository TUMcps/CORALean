module

public import CORALean.ContDynamics.LinParamSys.Definitions.API
public import CORALean.ContDynamics.LinParamSys.Instances
public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinParamSys.Operations.API
public import CORALean.ContDynamics.LinParamSys.Theorems.API

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

`'varParam'` is enclosed two ways: input-free by the box's own step, CORA's
`expmIndMixed` and `priv_tie`, through a Peano–Baker expansion of the run; and
with an input by freezing one member and paying the mismatch into the input set.

`Instances` is `Reach`'s, at `ℐ`: `LinearSys`'s windowed instances,
`ConstTrajectory` in place of `Trajectory`.
-/
