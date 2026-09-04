import CORALean.ContDynamics.NonlinearSysDT.LinStep
import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT
import CORALean.ContDynamics.NonlinearSysDT.Operations
import CORALean.ContDynamics.NonlinearSysDT.Theorems.API

/-!
# Discrete-time nonlinear systems, collected

The representation and what a trajectory of it is, then reachability by
re-linearization: `LinStep` certifies against `sys.f` with `AbstractionError`
and `linInput`, both stated over the map rather than a system, so nothing here
claims a flow that a discrete step does not have. `Operations` runs
`LinearSysDT.reach` one step per linearization, and `Theorems` shows the loop
contains every trajectory.

No `Δt`, no `discretize`, no `MatExp`: a discrete step is already what
`LinearSysDT` steps with, so nothing here converts a continuous system into
one.
-/
