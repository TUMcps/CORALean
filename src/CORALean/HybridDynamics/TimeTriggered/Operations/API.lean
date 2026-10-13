module

public import CORALean.HybridDynamics.TimeTriggered.Operations.DirectConversion
public import CORALean.HybridDynamics.TimeTriggered.Operations.ScalingConversion
public import CORALean.HybridDynamics.TimeTriggered.Operations.SingleMode
public import CORALean.HybridDynamics.TimeTriggered.Operations.SpaceTriggered

/-!
# The automata of the time-triggered conversion

`spaceTriggered` is the two-mode automaton of [1, Assumption 1, Assumption 2],
`directConversion` its conversion `H_tt` of [1, Sec. 3.1], `singleMode` and `scalingConversion`
the single-mode automaton and its dynamics scaling `H_scaling` of [1, Sec. 3.2].

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/
