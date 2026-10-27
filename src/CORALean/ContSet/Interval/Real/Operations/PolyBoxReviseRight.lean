module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `Interval.polyBoxReviseRight`

[1, Sec. 3 (three cases)] computes the left bound and leaves the right one to "a symmetric
process": the same three cases at `x̅`, the bound becoming the largest root of the selected
extremal function in `[x]`. The search is the argument `root`, held to
`Interval.IsRightRootBound`.

## Inputs
* `gLo` – lower polynomial bound
* `gHi` – upper polynomial bound
* `root` – root search procedure
* `xl` – lower end of the coordinate
* `xu` – upper end of the coordinate

## Output
* new upper end of the contracted coordinate

## References

* [1] [G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". Principles and Practice of Constraint Programming – CP 2010,
      2010.](../../../../../../references/2010/trombettoni-cp-box-consistency.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The right bound `r` of `[x̲, x̅]`, the three cases read at `x̅`. -/
noncomputable def Interval.polyBoxReviseRight (gLo gHi : ℝ → ℝ) (root : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (xl xu : ℝ) : ℝ :=
  if gLo xu ≤ 0 ∧ 0 ≤ gHi xu then xu                -- 1. no contraction
  else if 0 < gLo xu then root gLo xl xu            -- 2. `g̲` selected
  else root gHi xl xu                               -- 3. `g̅(x̅) < 0`: `g̅` selected

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
