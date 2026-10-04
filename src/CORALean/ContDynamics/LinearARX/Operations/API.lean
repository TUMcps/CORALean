import CORALean.ContDynamics.LinearARX.Operations.ComputeGO
import CORALean.ContDynamics.LinearARX.Operations.ComputeGOFloat
import CORALean.ContDynamics.LinearARX.Operations.SumRangeFloat
import CORALean.ContDynamics.LinearARX.Operations.Aext
import CORALean.ContDynamics.LinearARX.Operations.Alg1
import CORALean.ContDynamics.LinearARX.Operations.Alg1State
import CORALean.ContDynamics.LinearARX.Operations.Alg2
import CORALean.ContDynamics.LinearARX.Operations.Alg2State
import CORALean.ContDynamics.LinearARX.Operations.Bext
import CORALean.ContDynamics.LinearARX.Operations.Btilde
import CORALean.ContDynamics.LinearARX.Operations.OfObserver
import CORALean.ContDynamics.LinearARX.Operations.Feed
import CORALean.ContDynamics.LinearARX.Operations.FeedBox
import CORALean.ContDynamics.LinearARX.Operations.InputMat
import CORALean.ContDynamics.LinearARX.Operations.InputSet
import CORALean.ContDynamics.LinearARX.Operations.OutputEq
import CORALean.ContDynamics.LinearARX.Operations.Simulate
import CORALean.ContDynamics.LinearARX.Operations.SimulateBoxFloat
import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT
import CORALean.ContDynamics.LinearARX.Operations.OfCharpoly

/-!
# Linear ARX models: the conversion

`ToLinearSysDT` stacks the last `p` outputs into the state, `InputMat` and
`InputSet` fold the `p+1` input lags into `LinearSysDT`'s input set, `Feed` is the
input signal that results and `OutputEq` reads `y(k)` back out of the window.

Lützow and Althoff (CDC 2023): `Aext`, `Bext` and `Btilde` are the window recursion's
parameters (Eq. 9-10), `Alg1`/`Alg2` the two reachability algorithms over plain sets, and
`OfObserver` the state-space-to-ARMAX conversion (Prop. 2).
-/
