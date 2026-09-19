import CORALean.ContDynamics.NonlinearSys.AbstrReach
import CORALean.ContDynamics.NonlinearSys.AbstractionError
import CORALean.ContDynamics.NonlinearSys.AdaptReach
import CORALean.ContDynamics.NonlinearSys.EstimateGain
import CORALean.ContDynamics.NonlinearSys.LinStep
import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.NonlinearSys.OptDeltat
import CORALean.ContDynamics.NonlinearSys.PolyAbstractionError
import CORALean.ContDynamics.NonlinearSys.Operations.API
import CORALean.ContDynamics.NonlinearSys.ReachSet
import CORALean.ContDynamics.NonlinearSys.TuneAbstrOrder
import CORALean.ContDynamics.NonlinearSys.Theorems.API

/-!
# Nonlinear systems, collected

The representation and what a trajectory of it is, and then reachability by
conservative linearization: `AbstractionError` is the certificate the method
runs on, `LinStep` is one linearization together with the certificate it was
issued for, `Operations` computes the linear system, the input set it has to be
given and the loop that re-linearizes, `ReachSet` is the set the flow actually
reaches, and `Theorems` shows a confined run is a run of the linear system,
chains the steps, and restates both on that set rather than on a run.

`PolyAbstractionError` is the same certificate for CORA's `alg = 'poly'`: the
error is a polynomial in the factors the initial set is written in rather than a
set around it, so splitting the set splits the error too.

`AbstrReach` is the on-the-fly abstraction loop itself and `AdaptReach` the
adaptively-tuned step built on it, with `OptDeltat`, `EstimateGain` and
`TuneAbstrOrder` the three tuning subroutines the latter runs.

What CORA obtains from an interval Hessian is asked for as a certificate
instead, so how the abstraction error was computed is outside the trusted base.
`AbstractionErrorOfHessian` is the only file here that differentiates `f`, and it
runs the other way: it *supplies* the certificate `AbstrErrLin` computes. Nothing
that spends a certificate imports it, so the chain above stays derivative-free.
-/
