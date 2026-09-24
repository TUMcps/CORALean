import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionAgree
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB

/-!
# `ConPolyZono.intersectionB`

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
def ConPolyZono.intersectionB (cPZ₁ cPZ₂ : ConPolyZono 𝕋 n) :
    Interval (Vec 𝕋 (cPZ₁.m + cPZ₂.m + n)) :=
  ⟨Fin.append (ConPolyZono.plusB cPZ₁.b cPZ₂.b).inf (ConPolyZono.intersectionAgree cPZ₁ cPZ₂).inf,
   Fin.append (ConPolyZono.plusB cPZ₁.b cPZ₂.b).sup (ConPolyZono.intersectionAgree cPZ₁ cPZ₂).sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
