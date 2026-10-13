import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.PolyZonotope.Float.Operations.Compact

/-!
# `ConPolyZono.mergedColUp`

The same fibre rounded the other way, which is what bounds the gap.
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

/-- The same fibre rounded the other way, which is what bounds the gap. -/
def ConPolyZono.mergedColUp (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep cPZ.E).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep cPZ.E) (fun i l => cPZ.G l i) i
    (PolyZonotope.keepIdx cPZ.E j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
