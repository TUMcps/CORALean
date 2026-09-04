import CORALean.ContDynamics.NonlinearSysDT.LinStep
import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT
import CORALean.ContDynamics.NonlinearSysDT.Operations
import CORALean.ContDynamics.NonlinearSysDT.Theorems.API

/-!
# Discrete-time nonlinear systems, collected

The representation and what a trajectory of it is, then reachability by
re-linearization: `LinStep` reuses `NonlinearSys`'s `AbstractionError` and
`linInput`, which read no more of a system than its field, `Operations` runs
`LinearSysDT.reach` one step per linearization, and `Theorems` shows the loop
contains every trajectory.

No `Δt`, no `discretize`, no `MatExp`: a discrete step is already what
`LinearSysDT` steps with, so nothing here converts a continuous system into
one.
-/
