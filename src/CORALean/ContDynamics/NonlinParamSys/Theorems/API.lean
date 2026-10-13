module

public import CORALean.ContDynamics.NonlinParamSys.Theorems.ConstTrajectoryToAugment
public import CORALean.ContDynamics.NonlinParamSys.Theorems.ConstTrajectoryToTrajectory
public import CORALean.ContDynamics.NonlinParamSys.Theorems.JacobianFamilyMem
public import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeFCounterexample
public import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeFMem
public import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeFloatF
public import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeFloatJacX
public import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeFloatJacU
public import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeJacUMem
public import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeJacXMem
public import CORALean.ContDynamics.NonlinParamSys.Theorems.LinReachCoraMissesCounterexample
public import CORALean.ContDynamics.NonlinParamSys.Theorems.LinReachCoraRemainderZero
public import CORALean.ContDynamics.NonlinParamSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.NonlinParamSys.Theorems.ReachFloatOuter
public import CORALean.ContDynamics.NonlinParamSys.Theorems.ReachFloatCheckedEqSome
public import CORALean.ContDynamics.NonlinParamSys.Theorems.ToNonlinParam
public import CORALean.ContDynamics.NonlinParamSys.Theorems.ToNonlinearSys
public import CORALean.ContDynamics.NonlinParamSys.Theorems.TrajectoryOfNonlinearSys
public import CORALean.ContDynamics.NonlinParamSys.Theorems.TrajectoryToNonlinParam
public import CORALean.ContDynamics.NonlinParamSys.Theorems.TrajectoryToNonlinearSys

/-!
# What `NonlinParamSys` guarantees

`ConstTrajectoryToTrajectory` is the two trajectory readings' relation to each
other; `ToNonlinParam` and `TrajectoryToNonlinParam` are the embedding from a
plain nonlinear system, its parameter ignored; `ToNonlinearSys` and the two
`Trajectory…NonlinearSys` files are the other embedding, reading the parameter
as an extra input, in both directions. `ConstTrajectoryToAugment` is the third,
the parameter as an extra state, and `ReachUnionOuter` what `reachUnion`
guarantees through it. `LinearizeFMem`, `LinearizeJacXMem` and `LinearizeJacUMem` (through
`JacobianFamilyMem`) say `linearize`'s zonotopes hold the dynamics and their Jacobians at every
parameter of the box when `f` is affine in `p`; `LinearizeFCounterexample` is the case it is not.
`LinReachCoraMissesCounterexample` follows it into one `linReach` step, where the state of the run
at `p = 2` is outside the set; `LinReachCoraRemainderZero` rules out the abstraction error covering
it.
-/
