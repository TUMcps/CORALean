import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactFactorsNominal

/-!
# `compactFactors` over-approximates, dropping unused factors

Costs nothing at all: `compactFactors_nominal` already is the exact equality.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.compactFactors_outer (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ PZ.compactFactors.construct :=
  InflatedContSet.mono_subset (PolyZonotope.compactFactors_nominal PZ).subset
    (subset_refl _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
