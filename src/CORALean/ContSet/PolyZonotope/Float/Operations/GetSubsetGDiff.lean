module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetGDown

@[expose] public section

/-!
# `PolyZonotope.getSubsetGDiff`

What the rounded-down generators of `getSubset` cost: the rounded-up entry minus the rounded-down
one, rounded up. Both bracket the exact entry, so the exact one is within this of the stored one.
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

def PolyZonotope.getSubsetGDiff (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) (cen rad : 𝕋) :
    Mat 𝕋 n (pZ.h * (pZ.maxExp k + 1)) := fun r l =>
  let f := pZ.getSubsetCoef k cen rad (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2
  subUp (Interval.mulHi f.inf f.sup (pZ.G (finProdFinEquiv.symm l).1 r)
    (pZ.G (finProdFinEquiv.symm l).1 r)) (pZ.getSubsetGDown k cen rad r l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
