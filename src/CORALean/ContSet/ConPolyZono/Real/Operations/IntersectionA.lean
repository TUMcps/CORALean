module

public import CORALean.ContSet.ConPolyZono.Real.Operations.AgreeRow
public import CORALean.ContSet.ConPolyZono.Real.Operations.Plus

@[expose] public section

/-!
# `ConPolyZono.intersectionA`

The constraint matrix of `intersectionDep`: the two systems block-diagonally over the
constraint columns and blind to the generator columns, then the agreement
rows, blind to the constraint columns.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The constraint matrix of `intersectionDep`: the two systems block-diagonally over the
constraint columns and blind to the generator columns, then the agreement rows,
blind to the constraint columns. -/
def ConPolyZono.intersectionA (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    Mat ℝ (cPZ₁.m + cPZ₂.m + n) (cPZ₁.s + cPZ₂.s + (cPZ₁.h + cPZ₂.h)) := fun i =>
  Fin.append
    (fun r => Fin.append (ConPolyZono.plusA cPZ₁.A cPZ₂.A r) (0 : Fin (cPZ₁.h + cPZ₂.h) → ℝ))
    (fun r => Fin.append (0 : Fin (cPZ₁.s + cPZ₂.s) → ℝ) (ConPolyZono.agreeRow cPZ₁ cPZ₂ r)) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
