import CORALean.HybridDynamics.TimeTriggered.Definitions.ContOverapprox
import CORALean.HybridDynamics.TimeTriggered.Definitions.FinalConversion
import CORALean.HybridDynamics.TimeTriggered.Definitions.FirstDwell
import CORALean.HybridDynamics.TimeTriggered.Definitions.OverapproxErrorLE
import CORALean.HybridDynamics.TimeTriggered.Definitions.SecondDwell

/-!
# What the time-triggered conversion is measured by

`FirstDwell` and `SecondDwell` are the selection of the two dwell times of [1, Sec. 3.1],
read as the properties the proof of `Lemma 1` uses. `ContOverapprox` is [1, Def. 8] and
`OverapproxErrorLE` [1, Def. 9], the error as a bound rather than a supremum. `finalConversion`
is `H_final` of [1, Sec. 3.3], real-valued through its scaling function and so a specification.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/
