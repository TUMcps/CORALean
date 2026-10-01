import CORALean.ContDynamics.LinearARX.Operations.Feed
import CORALean.ContDynamics.LinearARX.Operations.InputMat
import CORALean.ContDynamics.LinearARX.Operations.InputSet
import CORALean.ContDynamics.LinearARX.Operations.OutputEq
import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT

/-!
# Linear ARX models: the conversion

`ToLinearSysDT` stacks the last `p` outputs into the state, `InputMat` and
`InputSet` fold the `p+1` input lags into `LinearSysDT`'s input set, `Feed` is the
input signal that results and `OutputEq` reads `y(k)` back out of the window.
-/
