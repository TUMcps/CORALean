module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# The part of an until interval one pair of runs gives

The first line of the loop body of `until.m`: `bint = ((lint(i) & rint(j)) - int) & lint(i)` for a
run `lint(i) = [a,b]` of the left signal, a run `rint(j) = [c,d]` of the right one and the
interval `int = [p,q]`. `&` of intervals (`and_`) takes the intersection of the bounds if the gap
`lb - ub` is at most `eps` (swapping the bounds if it is negative) and is empty otherwise, `-`
subtracts the bounds crosswise. The result is `none` if `bint` is empty, else its bounds; the
upper bound `q` may be infinite.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bounds of `bint = ((lint(i) & rint(j)) - int) & lint(i)`, `none` if it is empty. -/
noncomputable def FiniteSignal.untilPiece (eps p : ℝ) (q : EReal) (L R : ℝ × ℝ) :
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
