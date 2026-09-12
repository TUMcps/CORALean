import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContDynamics.LinearSys.MatExp.ExactIntervalEnclosures
import CORALean.ContDynamics.LinearSys.MatExp.ExactSecondOrder
import CORALean.ContDynamics.LinearSys.MatExp.ExpRemainderOrder
import CORALean.ContDynamics.LinearSys.MatExp.ExpRemainderStep
import CORALean.ContDynamics.LinearSys.MatExp.IntervalCorrection
import CORALean.ContDynamics.LinearSys.MatExp.IntervalEnclosures
import CORALean.ContDynamics.LinearSys.MatExp.MatZonoEnclosures
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.API

/-!
# Enclosing a matrix exponential, collected

What a discretization needs and nothing else uses: `e^{AΔt}` is transcendental,
so a step is taken against an interval matrix around it rather than against it.
`IntervalEnclosures` widens `Enclosures` to a whole interval matrix, at the
usual dependency-loss cost of interval arithmetic, and `IntervalCorrection`
widens the two objects a continuous-time step needs besides the exponential —
the correction matrix and the input remainder — the same way.
`MatZonoEnclosures` is CORA's `expmInd`, which pays that cost on the remainder
alone and keeps the Taylor sum as a matrix zonotope. `ExactSecondOrder` and
`ExactIntervalEnclosures` pay it on orders three and up only, the second-order
term being exactly computable, and enclose more narrowly for it.

`ExpRemainderOrder` and `ExpRemainderStep` run the choice the other way: they
take an admissible error and name a parameter meeting it, rather than taking a
parameter and reporting the bound. That is one step of adaptive parameter
tuning and not the algorithm — the error bounded is the exponential's, not the
reachable set's.

Enclosures only, no representation — an interval matrix is `Interval (Mat ℝ m n)`
like any other set.
-/
