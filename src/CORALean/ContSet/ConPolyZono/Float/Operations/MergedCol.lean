import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.PolyZonotope.Float.Operations.Compact

/-!
# `ConPolyZono.mergedCol`

The merged generator column as stored: the lower of the two directed fibre
sums, `repKeep` naming the one column per class that survives.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The merged generator column as stored: the lower of the two directed fibre
sums, `repKeep` naming the one column per class that survives. -/
def ConPolyZono.mergedCol (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep cPZ.E).card) : 𝕋 :=
  PolyZonotope.fiberDown (Real.PolyZonotope.rep cPZ.E) (fun i l => cPZ.G l i) i
    (PolyZonotope.keepIdx cPZ.E j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
