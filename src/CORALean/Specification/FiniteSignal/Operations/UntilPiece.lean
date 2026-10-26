module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# The piece a pair of runs gives in the until of finite signals

The bounds of `bint = ((lint(i) & rint(j)) - int) & lint(i)` in `until.m`, for a run `L` of the left
signal and a run `R` of the right one: their meet (`&` with the tolerance `eps`), shifted back by
the until interval `[p,q]` and met with `L` again; `none` if it is empty beyond the tolerance.
Real-only, a specification: it computes on real time stamps exactly; its rounded refinement,
inside it, is the piece of `FiniteSignal.untilFloat?`.

## Inputs
* `eps` – machine epsilon
* `p` – interval lower bound
* `q` – interval upper bound
* `L` – run of the left signal
* `R` – run of the right signal

## Output
* the bounds of the piece, or none if it is empty
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bounds of `bint = ((lint(i) & rint(j)) - int) & lint(i)`, `none` if it is empty. -/
noncomputable def FiniteSignal.untilPiece (eps p : ℝ) (q : EReal) (L R : Real.Interval ℝ) :
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
