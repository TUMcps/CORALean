module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetCoef

@[expose] public section

/-!
# `PolyZonotope.getSubsetGDown`

The generators of `getSubset`: the column's generator scaled by the bracketed coefficient, each
entry rounded down. The exact entry is at most `getSubsetGDiff` above it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.getSubsetGDown (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) (cen rad : 𝕋) :
    Mat 𝕋 n (pZ.h * (pZ.maxExp k + 1)) := fun r l =>
  let f := pZ.getSubsetCoef k cen rad (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2
  Interval.mulLo f.inf f.sup (pZ.G (finProdFinEquiv.symm l).1 r) (pZ.G (finProdFinEquiv.symm l).1 r)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
