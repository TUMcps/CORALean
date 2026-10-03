import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetGDown

/-!
# `PolyZonotope.getSubsetGDiff`

What the rounded-down generators of `getSubset` cost: the rounded-up entry minus the rounded-down
one, rounded up. Both bracket the exact entry, so the exact one is within this of the stored one.
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

def PolyZonotope.getSubsetGDiff (pZ : PolyZonotope 𝕋 n) (k : Fin pZ.p) (cen rad : 𝕋) :
    Mat 𝕋 n (pZ.h * (pZ.maxExp k + 1)) := fun r l =>
  let f := pZ.getSubsetCoef k cen rad (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2
  subUp (Interval.mulHi f.1 f.2 (pZ.G r (finProdFinEquiv.symm l).1)
    (pZ.G r (finProdFinEquiv.symm l).1)) (pZ.getSubsetGDown k cen rad r l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
