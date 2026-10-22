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

`sig = until(lsig,int,rsig)` of `until.m` with the defaults `low = false`, `up = true`: the signals
need the same duration (else CORA throws, here `none`); the result starts false and is or-ed, for
each run of the left signal and each run of the right one, with the indicator of `((lint(i) &
rint(j)) - int) & lint(i)`. `int = [p,q]` is given by its bounds, `eps` is MATLAB's `eps`.
Refinement pending: CORA computes this in doubles, its refinement over `𝕋` is not yet written.

## Inputs
* `eps` – machine epsilon
* `lsig` – left signal
* `p` – interval lower bound
* `q` – interval upper bound
* `rsig` – right signal

## Output
* the until signal, or none if the durations differ
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The bounds of `bint = ((lint(i) & rint(j)) - int) & lint(i)`, `none` if it is empty. -/
noncomputable def FiniteSignal.aux_untilPiece (eps p : ℝ) (q : EReal) (L R : Real.Interval ℝ) :
    Option (Real.Interval ℝ) :=
  -- lint(i) & rint(j)
  let lb := Max.max L.inf R.inf
  let ub := Min.min L.sup R.sup
  if ¬ lb - ub ≤ eps then none
  else
    -- (lint(i) & rint(j)) - int
    let n1 : EReal := (Min.min lb ub : ℝ) - q
    let n2 : EReal := (Max.max lb ub : ℝ) - p
    -- & lint(i)
    let lb' : EReal := Max.max n1 L.inf
    let ub' : EReal := Min.min n2 L.sup
    if ¬ lb' - ub' ≤ eps then none
    else some ⟨(Min.min lb' ub').toReal, (Max.max lb' ub').toReal⟩

/-- The loop body for the runs `LR = (lint(i), rint(j))`. -/
noncomputable def FiniteSignal.aux_untilStep (eps p : ℝ) (q : EReal) (dur : ℝ)
    (sig : FiniteSignal ℝ Bool) (LR : Real.Interval ℝ × Real.Interval ℝ) :
    Option (FiniteSignal ℝ Bool) :=
  match FiniteSignal.aux_untilPiece eps p q LR.1 LR.2 with
  | none => some sig
  -- if ~representsa_(bint,'emptySet',eps) && volume(bint) > 0
  | some ⟨lo, hi⟩ =>
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
