module

public import CORALean.ContSet.Interval.Real.Operations.EBox

@[expose] public section

/-!
# `Interval.EBox.construct`

The points of `ℝⁿ` whose every coordinate lies between the two `EReal` bounds of an
`Interval.EBox`.

## Inputs
* `B` – extended box

## Output
* the set of points between the extended bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The points whose every coordinate lies between the two bounds. -/
def Interval.EBox.construct (B : Interval.EBox n) : Set (Vec ℝ n) :=
  {x | ∀ i, B.1 i ≤ ((x i : ℝ) : EReal) ∧ ((x i : ℝ) : EReal) ≤ B.2 i}


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
