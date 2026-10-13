import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.PolyZonotope.Real.Operations.BilinOuter

/-!
# `PolyZonotope.matMap`

CORA's `matMap(pZ1, pZ2, n, k, m)`: the product of an `n × k` and a `k × m` matrix polynomial
zonotope. The dependent part is `bilin` at matrix multiplication, exact; the independent
generators CORA carries (`GI1 c2`, `c1 GI2`, `GI1 GI2`, `G1 GI2`, `GI1 G2`) are the cross terms
`bilinOuter` adds, so the whole is an enclosure.

The factors are shared positionally, as in `bilin`, which is what CORA's `mergeExpMatrix` makes of
two sets that name the same ids; two sets over different factors are padded to a common set first
(`padBack`, `padFront`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The product of two matrix polynomial zonotopes over shared factors. -/
def PolyZonotope.matMap (pZ₁ : PolyZonotope (Mat ℝ n k)) (pZ₂ : PolyZonotope (Mat ℝ k m))
    (hp : pZ₁.p = pZ₂.p) : PolyZonotope (Mat ℝ n m) :=
  pZ₁.bilinOuter matMulBilin pZ₂ hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
