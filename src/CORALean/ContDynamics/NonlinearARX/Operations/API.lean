import CORALean.ContDynamics.NonlinearARX.Operations.Feed
import CORALean.ContDynamics.NonlinearARX.Operations.OutputSel
import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDT

/-!
# Nonlinear ARX models: the conversion

`ToNonlinearSysDT` stacks the last `p` outputs into the state and the `p+1` input
lags into the input, `Feed` is the input signal that results and `OutputSel` reads
`y(k)` back out of the window.
-/
