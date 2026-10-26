module

public import CORALean.HybridDynamics.TimeTriggered.Theorems.DirectConversionOverapprox
public import CORALean.HybridDynamics.TimeTriggered.Theorems.IsExecFlowTimer
public import CORALean.HybridDynamics.TimeTriggered.Theorems.FinalConversionContOverapprox
public import CORALean.HybridDynamics.TimeTriggered.Theorems.FinalConversionNotErrorLt
public import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsOfHasDerivAt
public import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsTimer
public import CORALean.HybridDynamics.TimeTriggered.Theorems.HasDerivWithinAtIciOfDeriv
public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolution
public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionConstOfZero
public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionUnique
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionClockLe
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionEqOrbit
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionNonneg
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionUnscale
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScalingConversionContOverapprox
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScalingConversionNotZeroError
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScalingConversionSubsetReach
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScalingConversionZeroError
public import CORALean.HybridDynamics.TimeTriggered.Theorems.SingleModeIsExecOfSolution
public import CORALean.HybridDynamics.TimeTriggered.Theorems.SingleModeExistsSolutionOfIsExec
public import CORALean.HybridDynamics.TimeTriggered.Theorems.SpaceTriggeredIsExecOrbit

/-!
# What the time-triggered conversion guarantees

`directConversion_overapprox` is [1, Lemma 1]. For [1, Lemma 2],
`scalingConversion_not_zeroError` is the counterexample to the printed zero-error claim and
`scalingConversion_zeroError` the corrected statement. `finalConversion_isContOverapprox` is
[1, Cor. 1] and `finalConversion_not_error_lt` the counterexample to [1, Thm. 1]. The ODE facts
below them: `lipschitzSolution` (existence for every horizon), `lipschitzSolution_unique`,
`scaledSolution_unscale` (the reparametrization), `scaledSolution_clock_le` (the scaled run
does not pass the guard) and the executions of the automata as solutions.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for Reachability
      Analysis of Hybrid Automata". Formal Modeling and Analysis of Timed Systems, 2017.
-/
