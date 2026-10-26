module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Combine
public import CORALean.Specification.FiniteSignal.Operations.FindIntervals
public import CORALean.Specification.FiniteSignal.Operations.Indicator
public import CORALean.Specification.FiniteSignal.Operations.Mk

@[expose] public section

/-!
# The until of two finite signals over a float scalar

`sig = until(lsig,int,rsig)` of `until.m`, as `until?`, with time stamps in `𝕋` and every rounding
turned so that the result is true only where the exact one is (`untilFloat?_inner`): the tolerance
test `lb - ub <= eps` takes the difference rounded up, the shifted bounds of
`(lint(i) & rint(j)) - int` round inward (the lower one up, the upper one down), and a piece whose
ends cross after the `& lint(i)` is dropped rather than turned around, as CORA's `min`/`max` of
the ends would. These are departures from CORA, which rounds to nearest (the departures table of
the coverage README); the comparisons are exact (`TimeOrder`).

## Inputs
* `eps` – machine epsilon
* `lsig` – left signal
* `p` – interval lower bound
* `q` – interval upper bound
* `rsig` – right signal

## Output
* the until signal, or none if the durations differ
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The bounds of `bint = ((lint(i) & rint(j)) - int) & lint(i)`, rounded inward, `none` if it is
empty. -/
def FiniteSignal.aux_untilPieceFloat (eps p : 𝕋) (q : WithTop 𝕋) (L R : Real.Interval 𝕋) :
    Option (Real.Interval 𝕋) :=
  -- lint(i) & rint(j)
  let lb := if L.inf ≤ R.inf then R.inf else L.inf
  let ub := if L.sup ≤ R.sup then L.sup else R.sup
  -- the tolerance test on the difference rounded up
  if ¬ subUp lb ub ≤ eps then none
  else
    -- (lint(i) & rint(j)) - int, the lower bound rounded up, the upper one down
    let lo := if lb ≤ ub then lb else ub
    let hi := if lb ≤ ub then ub else lb
    let n2 := subDown hi p
    -- & lint(i); `min(lb,ub) - inf` is below every time
    let lb' := match q with
      | none => L.inf
      | some y => if subUp lo y ≤ L.inf then L.inf else subUp lo y
    let ub' := if n2 ≤ L.sup then n2 else L.sup
    if lb' < ub' then some ⟨lb', ub'⟩ else none

/-- The loop body for the runs `LR = (lint(i), rint(j))`. -/
def FiniteSignal.aux_untilStepFloat (eps p : 𝕋) (q : WithTop 𝕋) (dur : 𝕋)
    (sig : FiniteSignal 𝕋 Bool) (LR : Real.Interval 𝕋 × Real.Interval 𝕋) :
    Option (FiniteSignal 𝕋 Bool) :=
  match FiniteSignal.aux_untilPieceFloat eps p q LR.1 LR.2 with
  | none => some sig
  -- if ~representsa_(bint,'emptySet',eps) && volume(bint) > 0
  | some ⟨lo, hi⟩ =>
    if lo < hi then
      -- sig = sig | finiteSignal.indicator(dur,bint,up)
      (FiniteSignal.indicator? dur lo hi true).bind fun ind =>
        FiniteSignal.combine? (fun x y => x || y) [sig, ind]
    else some sig


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = until(lsig,int,rsig)`, true only where the exact until is. -/
def FiniteSignal.untilFloat? (eps : 𝕋) (lsig : FiniteSignal 𝕋 Bool) (p : 𝕋) (q : WithTop 𝕋)
    (rsig : FiniteSignal 𝕋 Bool) : Option (FiniteSignal 𝕋 Bool) :=
  -- check duration of both signals
  if ¬ TimeOrder.Eqv lsig.duration rsig.duration then none
  else
    -- start with empty signal: sig = finiteSignal(dur,low)
    (FiniteSignal.mk? [lsig.duration] [false]).bind fun sig =>
      -- find intervals with matching values
      let lint := lsig.findIntervals (fun v => decide (true ≤ v))
      let rint := rsig.findIntervals (fun v => decide (true ≤ v))
      -- iterate over all combinations of intervals
      (lint.flatMap fun L => rint.map fun R => (L, R)).foldlM
        (FiniteSignal.aux_untilStepFloat eps p q lsig.duration) sig

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
