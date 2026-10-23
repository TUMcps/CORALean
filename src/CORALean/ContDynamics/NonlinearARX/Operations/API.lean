module

public import CORALean.ContDynamics.NonlinearARX.Operations.ComputeGO
public import CORALean.ContDynamics.NonlinearARX.Operations.ComputeGOFloat
public import CORALean.ContDynamics.NonlinearARX.Operations.Feed
public import CORALean.ContDynamics.NonlinearARX.Operations.OutputSel
public import CORALean.ContDynamics.NonlinearARX.Operations.Simulate
public import CORALean.ContDynamics.NonlinearARX.Operations.SimulateBoxFloat
public import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDT
public import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDTFloat
public import CORALean.ContDynamics.NonlinearARX.Operations.FloatJacModelToNonlinearSysDTFloat
public import CORALean.ContDynamics.NonlinearARX.Operations.RevBlocks

/-!
# Nonlinear ARX models: the conversion

`ToNonlinearSysDT` stacks the last `p` outputs into the state and the `p+1` input
lags into the input, `Feed` is the input signal that results and `OutputSel` reads
`y(k)` back out of the window. `ComputeGO` is the output-error linearization of the converted
system along a reference run.
-/
