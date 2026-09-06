import CORALean.ContSet.ConPolyZono.Real.Operations.AgreeRow
import CORALean.ContSet.ConPolyZono.Real.Operations.Plus

/-!
# `ConPolyZono.andA`

The constraint matrix of `andDep`: the two systems block-diagonally over the
constraint columns and blind to the generator columns, then the agreement
rows, blind to the constraint columns.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The constraint matrix of `andDep`: the two systems block-diagonally over the
constraint columns and blind to the generator columns, then the agreement rows,
blind to the constraint columns. -/
def ConPolyZono.andA (C₁ C₂ : ConPolyZono (Vec ℝ n)) :
    Mat ℝ (C₁.m + C₂.m + n) (C₁.s + C₂.s + (C₁.h + C₂.h)) := fun i =>
  Fin.append
    (fun r => Fin.append (ConPolyZono.plusA C₁.A C₂.A r) (0 : Fin (C₁.h + C₂.h) → ℝ))
    (fun r => Fin.append (0 : Fin (C₁.s + C₂.s) → ℝ) (ConPolyZono.agreeRow C₁ C₂ r)) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
