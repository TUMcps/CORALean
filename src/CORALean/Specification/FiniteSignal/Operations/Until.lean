module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.FindIntervals
public import CORALean.Specification.FiniteSignal.Operations.Mk
public import CORALean.Specification.FiniteSignal.Operations.UntilStep

@[expose] public section

/-!
# The until of two finite signals

`sig = until(lsig,int,rsig)` of `until.m` with the default `low = false` and `up = true`: the
signals must have the same duration (CORA throws, here `none`); the result starts as the constant
false signal and, for every pair of a run of the left signal (`findIntervals(lsig,@(v) v >= up)`)
and a run of the right one, is or-ed with the indicator of `((lint(i) & rint(j)) - int) &
lint(i)`. The interval `int = [p,q]` is given by its bounds, `q` possibly infinite; `eps` is
MATLAB's machine epsilon. The options `low` and `up` are not modelled. Every `none` of a step is a
failure of a CORA call.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = until(lsig,int,rsig)`. -/
protected noncomputable def FiniteSignal.until? (eps : ℝ) (lsig : FiniteSignal ℝ Bool) (p : ℝ)
    (q : EReal) (rsig : FiniteSignal ℝ Bool) : Option (FiniteSignal ℝ Bool) :=
  -- check duration of both signals
  if lsig.duration ≠ rsig.duration then none
  else
    -- start with empty signal: sig = finiteSignal(dur,low)
    (FiniteSignal.mk? [lsig.duration] [false]).bind fun sig =>
      -- find intervals with matching values
      let lint := lsig.findIntervals (fun v => decide (true ≤ v))
      let rint := rsig.findIntervals (fun v => decide (true ≤ v))
      -- iterate over all combinations of intervals
      (lint.flatMap fun L => rint.map fun R => (L, R)).foldlM
        (FiniteSignal.untilStep eps p q lsig.duration) sig

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
