import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset

/-!
# `PolyZonotope.splitDepFactor`, over a floating-point scalar

The halves `αₖ ∈ [-1, 0]` and `αₖ ∈ [0, 1]` of `pZ`, each over the full factor domain: `getSubset`
at the centres `∓1/2` and radius `1/2`, all exact in the scalar (`half` is exact).
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

def PolyZonotope.splitDepFactor (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) :
    PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n) :=
  (pZ.getSubset k (neg (half one)) (half one), pZ.getSubset k (half one) (half one))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
