module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Combine
public import CORALean.Specification.FiniteSignal.Operations.FindIntervals
public import CORALean.Specification.FiniteSignal.Operations.Indicator
public import CORALean.Specification.FiniteSignal.Operations.Mk
public import Mathlib.Data.EReal.Operations

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

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The bounds of `bint = ((lint(i) & rint(j)) - int) & lint(i)`, `none` if it is empty. -/
noncomputable def FiniteSignal.aux_untilPiece (eps p : ℝ) (q : EReal) (L R : ℝ × ℝ) :
    Option (ℝ × ℝ) :=
  -- lint(i) & rint(j)
  let lb := Max.max L.1 R.1
  let ub := Min.min L.2 R.2
  if ¬ lb - ub ≤ eps then none
  else
    -- (lint(i) & rint(j)) - int
    let n1 : EReal := (Min.min lb ub : ℝ) - q
    let n2 : EReal := (Max.max lb ub : ℝ) - p
    -- & lint(i)
    let lb' : EReal := Max.max n1 L.1
    let ub' : EReal := Min.min n2 L.2
    if ¬ lb' - ub' ≤ eps then none
    else some ((Min.min lb' ub').toReal, (Max.max lb' ub').toReal)

/-- The loop body for the runs `LR = (lint(i), rint(j))`. -/
noncomputable def FiniteSignal.aux_untilStep (eps p : ℝ) (q : EReal) (dur : ℝ)
    (sig : FiniteSignal ℝ Bool) (LR : (ℝ × ℝ) × (ℝ × ℝ)) : Option (FiniteSignal ℝ Bool) :=
  match FiniteSignal.aux_untilPiece eps p q LR.1 LR.2 with
  | none => some sig
  -- if ~representsa_(bint,'emptySet',eps) && volume(bint) > 0
  | some (lo, hi) =>
    if lo < hi then
      -- sig = sig | finiteSignal.indicator(dur,bint,up)
      (FiniteSignal.indicator? dur lo hi true).bind fun ind =>
        FiniteSignal.combine? (fun x y => x || y) [sig, ind]
    else some sig


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
        (FiniteSignal.aux_untilStep eps p q lsig.duration) sig

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
