import CORALean.ContDynamics.NonlinearARX.Operations.ComputeGO
import CORALean.ContDynamics.NonlinearARX.Operations.ComputeGOFloat
import CORALean.ContDynamics.NonlinearARX.Operations.Feed
import CORALean.ContDynamics.NonlinearARX.Operations.FeedFloat
import CORALean.ContDynamics.NonlinearARX.Operations.OutputSel
import CORALean.ContDynamics.NonlinearARX.Operations.Simulate
import CORALean.ContDynamics.NonlinearARX.Operations.SimulateBoxFloat
import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDT
import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDTFloat
import CORALean.ContDynamics.NonlinearARX.Operations.FloatJacModelToNonlinearSysDTFloat

/-!
# Nonlinear ARX models: the conversion

`ToNonlinearSysDT` stacks the last `p` outputs into the state and the `p+1` input
lags into the input, `Feed` is the input signal that results and `OutputSel` reads
`y(k)` back out of the window. `ComputeGO` is the output-error linearization of the converted
system along a reference run.
-/
