import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetCoef

/-!
# `PolyZonotope.getSubsetGDown`

The generators of `getSubset`: the column's generator scaled by the bracketed coefficient, each
entry rounded down. The exact entry is at most `getSubsetGDiff` above it.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.getSubsetGDown (pZ : PolyZonotope 𝕋 n) (k : Fin pZ.p) (cen rad : 𝕋) :
    Mat 𝕋 n (pZ.h * (pZ.maxExp k + 1)) := fun r l =>
  let f := pZ.getSubsetCoef k cen rad (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2
  Interval.mulLo f.1 f.2 (pZ.G r (finProdFinEquiv.symm l).1) (pZ.G r (finProdFinEquiv.symm l).1)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
