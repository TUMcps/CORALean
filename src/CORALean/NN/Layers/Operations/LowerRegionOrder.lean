import CORALean.NN.Layers.Operations.RegionPolyOfRelaxation

/-!
# Trying lower orders on a region
The loop `for o = order-1:-1:0` of CORA's `findRegionPolys`: refit the region at order
`o`, keep the fit while its error is strictly under the tolerance, and stop at the first order
that is not. `k` orders remain, from `k - 1` down; the fit is the supplied relaxation's, standing
for `computeApproxPoly` with its error.
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

/-- The lowest-order fit of `[l, u]` the loop reaches from the current one `cur`. -/
def lowerRegionOrder (F : (o : ℕ) → PolyRelaxation 𝕋 o) (tol l u : 𝕋) :
    ℕ → RegionPoly 𝕋 → RegionPoly 𝕋
  | 0, cur => cur
  | k + 1, cur =>
    if ltStrict ((F k).error l u) tol then
      lowerRegionOrder F tol l u k (RegionPoly.ofRelaxation (F k) l u)
    else cur

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
