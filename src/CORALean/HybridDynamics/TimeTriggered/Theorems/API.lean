import CORALean.HybridDynamics.TimeTriggered.Theorems.DirectConversionOverapprox
import CORALean.HybridDynamics.TimeTriggered.Theorems.ExecFlowTimer
import CORALean.HybridDynamics.TimeTriggered.Theorems.FinalConversionContOverapprox
import CORALean.HybridDynamics.TimeTriggered.Theorems.FinalConversionNotErrorLt
import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsOfHasDerivAt
import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsSplit
import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsTimer
import CORALean.HybridDynamics.TimeTriggered.Theorems.HasDerivWithinAtIciOfDeriv
import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzPieceEq
import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolution
import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionConstOfZero
import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionLocal
import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionUnique
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionClockLe
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionEqOrbit
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionNonneg
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionUnscale
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScalingConversionContOverapprox
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScalingConversionNotZeroError
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScalingConversionSubsetReach
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScalingConversionZeroError
import CORALean.HybridDynamics.TimeTriggered.Theorems.SingleModeExecOfSolution
import CORALean.HybridDynamics.TimeTriggered.Theorems.SingleModeExistsSolutionOfExec
import CORALean.HybridDynamics.TimeTriggered.Theorems.SpaceTriggeredExecOrbit

/-!
# What the time-triggered conversion guarantees

`directConversion_overapprox` is [1, Lemma 1]. For [1, Lemma 2],
`scalingConversion_not_zeroError` is the counterexample to the printed zero-error claim and
`scalingConversion_zeroError` the corrected statement. `finalConversion_contOverapprox` is
[1, Cor. 1] and `finalConversion_not_error_lt` the counterexample to [1, Thm. 1]. The ODE facts
below them: `lipschitzSolution` (existence for every horizon), `lipschitzSolution_unique`,
`scaledSolution_unscale` (the reparametrization), `scaledSolution_clock_le` (the scaled run
does not pass the guard) and the executions of the automata as solutions.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/
