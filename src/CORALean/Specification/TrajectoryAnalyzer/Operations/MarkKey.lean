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
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sigs(k) = sigs(k) | finiteSignal.indicator(dur,interval(lo,hi),true)`. -/
noncomputable def TrajectoryAnalyzer.markKey (dur lo hi : ℝ)
    (sigs : List (String × FiniteSignal ℝ Bool)) (k : String) :
    Option (List (String × FiniteSignal ℝ Bool)) :=
  (sigs.lookup k).bind fun sig => (FiniteSignal.indicator? dur lo hi true).bind fun ind =>
    (FiniteSignal.combine? (· || ·) [sig, ind]).map fun sig' => replaceKey sigs k sig'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
