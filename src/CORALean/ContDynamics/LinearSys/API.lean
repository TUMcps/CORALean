import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.API
import CORALean.ContDynamics.LinearSys.Operations.API
import CORALean.ContDynamics.LinearSys.Theorems.API

/-!
# Continuous-time linear systems, collected

The system and what it denotes in `LinearSys`, sampling in `Operations`, the
closed form of a trajectory and what `reach` then guarantees in `Theorems`.

Reachability holds at the sample times, by sampling into `LinearSysDT`, or, once
`e^{AΔt}` is only enclosed rather than computed, into `LinParamSysDT`. Between
the sample times it is open: that needs a set enclosing the curve over a step.
-/
