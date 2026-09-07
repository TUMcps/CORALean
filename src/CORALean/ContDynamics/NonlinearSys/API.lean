import CORALean.ContDynamics.NonlinearSys.AbstractionError
import CORALean.ContDynamics.NonlinearSys.LinStep
import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContDynamics.NonlinearSys.PolyAbstractionError
import CORALean.ContDynamics.NonlinearSys.Operations.API
import CORALean.ContDynamics.NonlinearSys.ReachSet
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

No derivative appears anywhere in the directory. What CORA obtains from an
interval Hessian is asked for as a certificate instead, so how the abstraction
error was computed is outside the trusted base.
-/
