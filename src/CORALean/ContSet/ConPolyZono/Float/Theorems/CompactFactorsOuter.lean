import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactors
import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactFactorsNominal
import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

/-!
# `compactFactors` over-approximates, dropping unused factors

Costs nothing at all: `compactFactors_nominal` already is the exact equality.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compactFactors_outer (cPZ : ConPolyZono 𝕋 n) :
    cPZ.construct ⊆ cPZ.compactFactors.construct :=
  InflatedContSet.mono_subset (ConPolyZono.compactFactors_nominal cPZ).subset (subset_refl _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
