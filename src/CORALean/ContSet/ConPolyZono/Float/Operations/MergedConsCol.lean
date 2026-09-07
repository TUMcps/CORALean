import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.PolyZonotope.Float.Operations.Compact

/-!
# `ConPolyZono.mergedConsCol`

The merged constraint column as stored, `A`'s rows read as the generator
matrix they are on the constraint side.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The merged constraint column as stored, `A`'s rows read as the generator
matrix they are on the constraint side. -/
def ConPolyZono.mergedConsCol (cPZ : ConPolyZono 𝕋 n) (i : Fin cPZ.m)
    (l : Fin (PolyZonotope.repKeep cPZ.EC).card) : 𝕋 :=
  PolyZonotope.fiberDown (Real.PolyZonotope.rep cPZ.EC) cPZ.A i (PolyZonotope.keepIdx cPZ.EC l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
