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

def ConPolyZono.mergedConsColUp (C : ConPolyZono 𝕋 n) (i : Fin C.m)
    (l : Fin (PolyZonotope.repKeep C.EC).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep C.EC) C.A i (PolyZonotope.keepIdx C.EC l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
