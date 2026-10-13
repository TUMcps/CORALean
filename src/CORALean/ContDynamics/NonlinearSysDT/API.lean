module

public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT
public import CORALean.ContDynamics.NonlinearSysDT.Definitions.API
public import CORALean.ContDynamics.NonlinearSysDT.Operations.API
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.API
public import CORALean.ContDynamics.NonlinearSysDT.Complexity.API
public import CORALean.ContDynamics.NonlinearSysDT.Instances

/-!
# Discrete-time nonlinear systems, collected

The representation and what a trajectory of it is, then reachability by
re-linearization: `LinStep` certifies against `sys.f` with `AbstractionError`
and `linInput`, both stated over the map rather than a system, so nothing here
claims a flow that a discrete step does not have. `Operations` runs
`LinearSysDT.reach` one step per linearization, `Theorems` shows the loop
contains every trajectory, and `Complexity/Time` prices the loop by using the linear run's
own bound at one step. `WithSteps` bundles the system with its linearizations and
checkable regions, and `Instances` makes that `Reach`, its region tests run at run time.

No `Δt`, no `discretize`, no `MatExp`: a discrete step is already what
`LinearSysDT` steps with, so nothing here converts a continuous system into
one.
-/
