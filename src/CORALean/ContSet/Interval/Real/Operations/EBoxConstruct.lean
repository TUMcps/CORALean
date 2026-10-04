import CORALean.ContSet.Interval.Real.Operations.EBox

/-!
# `Interval.EBox.construct`

The points of `ℝⁿ` whose every coordinate lies between the two `EReal` bounds of an
`Interval.EBox`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The points whose every coordinate lies between the two bounds. -/
def Interval.EBox.construct (B : Interval.EBox n) : Set (Vec ℝ n) :=
  {x | ∀ i, B.1 i ≤ ((x i : ℝ) : EReal) ∧ ((x i : ℝ) : EReal) ≤ B.2 i}


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
