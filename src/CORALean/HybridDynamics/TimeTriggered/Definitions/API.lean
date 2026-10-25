module

public import CORALean.HybridDynamics.TimeTriggered.Definitions.IsContOverapprox
public import CORALean.HybridDynamics.TimeTriggered.Definitions.FinalConversion
public import CORALean.HybridDynamics.TimeTriggered.Definitions.IsFirstDwell
public import CORALean.HybridDynamics.TimeTriggered.Definitions.IsOverapproxErrorLE
public import CORALean.HybridDynamics.TimeTriggered.Definitions.IsSecondDwell

/-!
# What the time-triggered conversion is measured by

`IsFirstDwell` and `IsSecondDwell` are the selection of the two dwell times of [1, Sec. 3.1],
read as the properties the proof of `Lemma 1` uses. `IsContOverapprox` is [1, Def. 8] and
`IsOverapproxErrorLE` [1, Def. 9], the error as a bound rather than a supremum. `finalConversion`
is `H_final` of [1, Sec. 3.3], real-valued through its scaling function and so a specification.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for Reachability
      Analysis of Hybrid Automata". Formal Modeling and Analysis of Timed Systems, 2017.
-/
