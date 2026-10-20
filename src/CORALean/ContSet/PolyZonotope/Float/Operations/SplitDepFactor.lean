module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset

@[expose] public section

/-!
# `PolyZonotope.splitDepFactor`, over a floating-point scalar

The halves `αₖ ∈ [-1, 0]` and `αₖ ∈ [0, 1]` of `pZ`, each over the full factor domain: `getSubset`
at the centers `∓1/2` and radius `1/2`, all exact in the scalar (`half` is exact).

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor index

## Output
* pair of polynomial zonotopes for the two halves of that factor
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.splitDepFactor (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) :
    PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n) :=
  (pZ.getSubset k (neg (half one)) (half one), pZ.getSubset k (half one) (half one))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
