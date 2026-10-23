module

public import CORALean.Global.ReplaceKey
public import CORALean.Specification.FiniteSignal.Operations.Combine
public import CORALean.Specification.FiniteSignal.Operations.Indicator
public import CORALean.Specification.TrajectoryAnalyzer.TrajectoryAnalyzer

@[expose] public section

/-!
# Marking a proposition true on an interval

`sigs(k) = sigs(k) | finiteSignal.indicator(dur,interval(lo,hi),true)`: the signal of proposition
`k` becomes true on the interval, as in `setPossiblyTrue` of the builder of the reach set analyzer.
CORA throws if there is no signal of key `k` or the interval is degenerate; here `none`.

Generic over the time type: at a float scalar nothing rounds, the comparisons being exact
(`TimeOrder`).

## Inputs
* `T` – time type
* `dur` – signal duration
* `lo` – interval lower bound
* `hi` – interval upper bound
* `sigs` – signal of each proposition
* `k` – proposition key

## Output
* the signals with the proposition marked true on the interval, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sigs(k) = sigs(k) | finiteSignal.indicator(dur,interval(lo,hi),true)`. -/
def TrajectoryAnalyzer.markKey {T : Type} [TimeOrder T] [Zero T] (dur lo hi : T)
    (sigs : List (String × FiniteSignal T Bool)) (k : String) :
    Option (List (String × FiniteSignal T Bool)) :=
  (sigs.lookup k).bind fun sig => (FiniteSignal.indicator? dur lo hi true).bind fun ind =>
    (FiniteSignal.combine? (· || ·) [sig, ind]).map fun sig' => replaceKey sigs k sig'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
