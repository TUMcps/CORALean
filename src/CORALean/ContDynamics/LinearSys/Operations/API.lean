import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosure
import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSum
import CORALean.ContDynamics.LinearSys.Operations.InputTerm
import CORALean.ContDynamics.LinearSys.Operations.StepInput
import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep

/-!
# What a continuous-time linear system computes

Sampling in `Discretize`, and then two enclosures of what happens inside a step:
`InputSolution` for what the input adds, `TimeIntervalStep` for where the
homogeneous flow goes. `StepInput` and `InputReach` are the exact quantities
those two are measured against; `StepInputConst` is `StepInput` at one held
vector rather than a whole signal.

`DiscretizeEnclosure` is `Discretize` again, its matrix only enclosed: `e^{AΔt}`
is transcendental, so where the exponential itself cannot be computed the
result is a `LinParamSysDT` over an interval matrix rather than a `LinearSysDT`.
-/
