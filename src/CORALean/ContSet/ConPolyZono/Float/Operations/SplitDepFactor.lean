import CORALean.ContSet.ConPolyZono.Float.Operations.GetSubset

/-!
# `ConPolyZono.splitDepFactor`, over a floating-point scalar

The halves `αₖ ∈ [-1, 0]` and `αₖ ∈ [0, 1]` of `cPZ`, each over the full factor domain: `getSubset`
at the centres `∓1/2` and radius `1/2`, all exact in the scalar (`half` is exact).
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

def ConPolyZono.splitDepFactor (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (k : Fin cPZ.p) :
    ConPolyZono 𝕋 (Vec 𝕋 n) × ConPolyZono 𝕋 (Vec 𝕋 n) :=
  (cPZ.getSubset k (neg (half one)) (half one), cPZ.getSubset k (half one) (half one))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
