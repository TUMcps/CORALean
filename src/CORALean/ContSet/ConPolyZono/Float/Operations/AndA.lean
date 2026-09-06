import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeRow
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA

/-!
# `ConPolyZono.andA`

The constraint matrix of `andDep`: the two systems block-diagonally over the
constraint columns and blind to the generator columns, then the agreement
rows, blind to the constraint columns.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The constraint matrix of `andDep`: the two systems block-diagonally over the
constraint columns and blind to the generator columns, then the agreement rows,
blind to the constraint columns. -/
def ConPolyZono.andA (C₁ C₂ : ConPolyZono 𝕋 n) :
    Mat 𝕋 (C₁.m + C₂.m + n) (C₁.s + C₂.s + (C₁.h + C₂.h)) := fun i =>
  Fin.append
    (fun r => Fin.append (ConPolyZono.plusA C₁.A C₂.A r) (fun _ => zero))
    (fun r => Fin.append (fun _ => zero) (ConPolyZono.agreeRow C₁ C₂ r)) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
