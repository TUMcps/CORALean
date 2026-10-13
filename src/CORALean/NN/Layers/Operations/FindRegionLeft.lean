module

public import CORALean.NN.Layers.Operations.LowerRegionOrder

@[expose] public section

/-!
# The left polynomial of a step of `findRegionPolys`
From the left end `l` of the uncovered domain, fit `[l, u_i]`, halving `u_i - l` while the error
exceeds the tolerance, and then try lower orders. A region narrower than the tolerance is
CORA's `CORA:notConverged` error, here `none`, as is running out of `fuel`, the loop's bound
(CORA's halving ends by itself, in floats of finite exponent range). Returns the region and its
right end.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The accepted region `[l, u_i]` with its right end `u_i`, or `none`. -/
def findRegionLeft (F : (o : ℕ) → PolyRelaxation 𝕋 o) (order : ℕ) (tol l : 𝕋) :
    ℕ → 𝕋 → Option (RegionPoly 𝕋 × 𝕋)
  | 0, _ => none
  | fuel + 1, ui =>
    if le ((F order).error l ui) tol then
      some (lowerRegionOrder F tol l ui order (RegionPoly.ofRelaxation (F order) l ui), ui)
    else
      let ui' := addUp l (half (subUp ui l))
      if ltStrict (subUp ui' l) tol then none else findRegionLeft F order tol l fuel ui'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
