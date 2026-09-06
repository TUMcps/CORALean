import CORALean.ContSet.ConPolyZono.Float.Operations.AndAgree
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB

/-!
# `ConPolyZono.andB`

The two systems' own bounds, then the agreement rows'.
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

/-- The two systems' own bounds, then the agreement rows'. -/
def ConPolyZono.andB (C₁ C₂ : ConPolyZono 𝕋 n) : Interval 𝕋 (C₁.m + C₂.m + n) :=
  ⟨Fin.append (ConPolyZono.plusB C₁.b C₂.b).inf (ConPolyZono.andAgree C₁ C₂).inf,
   Fin.append (ConPolyZono.plusB C₁.b C₂.b).sup (ConPolyZono.andAgree C₁ C₂).sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
