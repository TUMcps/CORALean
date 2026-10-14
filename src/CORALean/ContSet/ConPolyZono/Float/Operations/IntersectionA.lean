module

public import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeRow
public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA

@[expose] public section

/-!
# `ConPolyZono.intersectionA`

The constraint matrix of `intersectionDep`: the two systems block-diagonally over the
constraint columns and blind to the generator columns, then the agreement
rows, blind to the constraint columns.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The constraint matrix of `intersectionDep`: the two systems block-diagonally over the
constraint columns and blind to the generator columns, then the agreement rows,
blind to the constraint columns. -/
def ConPolyZono.intersectionA (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    Mat 𝕋 (cPZ₁.m + cPZ₂.m + n) (cPZ₁.q + cPZ₂.q + (cPZ₁.h + cPZ₂.h)) := fun i =>
  Fin.append
    (fun r => Fin.append (ConPolyZono.plusA cPZ₁.A cPZ₂.A r) (fun _ => zero))
    (fun r => Fin.append (fun _ => zero) (ConPolyZono.agreeRow cPZ₁ cPZ₂ r)) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
