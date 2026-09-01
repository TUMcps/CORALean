import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.Operations
import CORALean.ContDynamics.LinearSys.Theorems.API

/-!
# Continuous-time linear systems, collected

The system and what it denotes in `LinearSys`, sampling in `Operations`, the
closed form of a trajectory and what `reach` then guarantees in `Theorems`.

Reachability holds at the sample times, by sampling into `LinearSysDT`. Between
them it is open: that needs a set enclosing the curve over a step.
-/
