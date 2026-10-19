module

public import CORALean.ContDynamics.LinearARX.Operations.ComputeGO
public import CORALean.ContDynamics.LinearARX.Operations.ComputeGOFloat
public import CORALean.ContDynamics.LinearARX.Operations.SumRangeFloat
public import CORALean.ContDynamics.LinearARX.Operations.Aext
public import CORALean.ContDynamics.LinearARX.Operations.Alg1
public import CORALean.ContDynamics.LinearARX.Operations.Alg2
public import CORALean.ContDynamics.LinearARX.Operations.Bext
public import CORALean.ContDynamics.LinearARX.Operations.Btilde
public import CORALean.ContDynamics.LinearARX.Operations.OfObserver
public import CORALean.ContDynamics.LinearARX.Operations.Basic
public import CORALean.ContDynamics.LinearARX.Operations.FeedBox
public import CORALean.ContDynamics.LinearARX.Operations.InputMat
public import CORALean.ContDynamics.LinearARX.Operations.InputSet
public import CORALean.ContDynamics.LinearARX.Operations.OutputEq
public import CORALean.ContDynamics.LinearARX.Operations.Simulate
public import CORALean.ContDynamics.LinearARX.Operations.SimulateBoxFloat
public import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT
public import CORALean.ContDynamics.LinearARX.Operations.OfCharpoly
public import CORALean.ContDynamics.LinearARX.Operations.Identify
public import CORALean.ContDynamics.LinearARX.Operations.IdentifyBlocks
public import CORALean.ContDynamics.LinearARX.Operations.IdentifyCandidate
public import CORALean.ContDynamics.LinearARX.Operations.IdentifyRegressor

/-!
# Linear ARX models: the conversion

`ToLinearSysDT` stacks the last `p` outputs into the state, `InputMat` and
`InputSet` fold the `p+1` input lags into `LinearSysDT`'s input set, `Feed` is the
input signal that results and `OutputEq` reads `y(k)` back out of the window.

Lützow and Althoff (CDC 2023): `Aext`, `Bext` and `Btilde` are the window recursion's
parameters (Eq. 9-10), `Alg1`/`Alg2` the two reachability algorithms over plain sets, and
`OfObserver` the state-space-to-ARMAX conversion (Prop. 2).

`identify` (algorithm `dmd`) is `Identify`, with `IdentifyRegressor`, `IdentifyCandidate` and
`IdentifyBlocks` its steps.
-/
