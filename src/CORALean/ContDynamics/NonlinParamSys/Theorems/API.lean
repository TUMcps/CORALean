import CORALean.ContDynamics.NonlinParamSys.Theorems.ConstTrajectoryToAugment
import CORALean.ContDynamics.NonlinParamSys.Theorems.ConstTrajectoryToTrajectory
import CORALean.ContDynamics.NonlinParamSys.Theorems.JacobianFamilyMem
import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeFCounterexample
import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeFMem
import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeJacUMem
import CORALean.ContDynamics.NonlinParamSys.Theorems.LinearizeJacXMem
import CORALean.ContDynamics.NonlinParamSys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.NonlinParamSys.Theorems.ReachFloatOuter
import CORALean.ContDynamics.NonlinParamSys.Theorems.ReachFloatCheckedEqSome
import CORALean.ContDynamics.NonlinParamSys.Theorems.ToNonlinParam
import CORALean.ContDynamics.NonlinParamSys.Theorems.ToNonlinearSys
import CORALean.ContDynamics.NonlinParamSys.Theorems.TrajectoryOfNonlinearSys
import CORALean.ContDynamics.NonlinParamSys.Theorems.TrajectoryToNonlinParam
import CORALean.ContDynamics.NonlinParamSys.Theorems.TrajectoryToNonlinearSys

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
-/
