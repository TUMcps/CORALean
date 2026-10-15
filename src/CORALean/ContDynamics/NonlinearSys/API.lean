module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import CORALean.ContDynamics.NonlinearSys.Definitions.API
public import CORALean.ContDynamics.NonlinearSys.Operations.API
public import CORALean.ContDynamics.NonlinearSys.Theorems.API
public import CORALean.ContDynamics.NonlinearSys.Counterexamples.API
public import CORALean.ContDynamics.NonlinearSys.Instances

/-!
# Nonlinear systems, collected

The representation and what a trajectory of it is, and then reachability by conservative
linearization: `AbstractionError` is the certificate the method runs on, `LinStep` is one
linearization together with the certificate it was issued for, `Operations` computes the linear
system, the input set it has to be given and the loop that re-linearizes, `ReachSet` is the set the
flow actually reaches, and `Theorems` shows a confined run is a run of the linear system, chains
the steps, and restates both on that set rather than on a run. `WithSteps` bundles a chain of steps
with checkable regions, and `Instances` makes it `Reach`, its tests run at run time.

`PolyAbstractionError` is the same certificate for CORA's `alg = 'poly'`: a polynomial in the
initial set's own factors rather than a set around it, so splitting the set splits the error too.

`AbstrReach` is the on-the-fly abstraction loop and `AdaptReach` the adaptively-tuned step on it,
with `OptDeltat`, `EstimateGain` and `TuneAbstrOrder` its subroutines; `CenterAbstrReach` is the
earlier paper's same loop at the center, `PolyReach` the HSCC'13 original it descends from, and
`TuneDeltat` its own tuning of the step.

What CORA obtains from an interval Hessian is asked for as a certificate
instead, so how the abstraction error was computed is outside the trusted base.
`AbstractionErrorOfHessian` and `EnclosesOfHasFDerivAt` are the only files here that
differentiate `f`, and both *supply* what the chain spends. `ReachFloat` is the float
run, linearizing itself from a `FloatModel` of `f` and certifying its own steps.
-/
