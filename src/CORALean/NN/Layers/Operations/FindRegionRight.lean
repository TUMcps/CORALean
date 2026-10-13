import CORALean.NN.Layers.Operations.RegionPolyOfRelaxation

/-!
# The right polynomial of a step of `findRegionPolys`
From the right end `u` of the uncovered domain, fit `[l_i, u]`, halving `u - l_i` while the error
exceeds the tolerance. No lower order is tried here, as in CORA. A region narrower than the
tolerance, or running out of `fuel`, is `none`. Returns the region and its left end.
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

/-- The accepted region `[l_i, u]` with its left end `l_i`, or `none`. -/
def findRegionRight (F : (o : ℕ) → PolyRelaxation 𝕋 o) (order : ℕ) (tol u : 𝕋) :
    ℕ → 𝕋 → Option (RegionPoly 𝕋 × 𝕋)
  | 0, _ => none
  | fuel + 1, li =>
    if le ((F order).error li u) tol then
      some (RegionPoly.ofRelaxation (F order) li u, li)
    else
      let li' := subDown u (half (subUp u li))
      if ltStrict (subUp u li') tol then none else findRegionRight F order tol u fuel li'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
