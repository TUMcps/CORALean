module

public import CORALean.HybridDynamics.TimeTriggered.DiffInclAutomaton
public import CORALean.HybridDynamics.TimeTriggered.Definitions.API
public import CORALean.HybridDynamics.TimeTriggered.Operations.API
public import CORALean.HybridDynamics.TimeTriggered.Theorems.API

/-!
# Time-triggered conversion of guards, collected

Bak, Bogomolov and Althoff's conversion of a space-triggered transition into time-triggered
ones, [1, Sec. 3.1] to [1, Sec. 3.3], over hybrid automata with differential-inclusion flows
(`DiffInclAutomaton`), which `HybridAutomaton`'s linear
locations do not model. `IsExec` carries the duration, so
`Reach≤T` is `reachLE T`. `Lemma 1` is proved as printed under the two dwell-time properties,
`Lemma 2`'s zero-error claim is false against `Reach≤T` and proved against `Reach`, `Cor. 1` is
proved, and `Thm. 1` is false: the dwell time in `m_either` does not shrink with the scaling.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/
