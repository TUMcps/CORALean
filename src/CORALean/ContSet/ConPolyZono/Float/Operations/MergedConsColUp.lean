import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.PolyZonotope.Float.Operations.Compact

/-!
# `ConPolyZono.mergedConsColUp`
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

def ConPolyZono.mergedConsColUp (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (i : Fin cPZ.m)
    (l : Fin (PolyZonotope.repKeep cPZ.EC).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep cPZ.EC) cPZ.A i (PolyZonotope.keepIdx cPZ.EC l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
