import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactConsOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactFactorsOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactGensOuter

/-!
# `compact` over-approximates, where the exact one is an equality

`compactGens` merges generator columns and rounds, `compactCons` merges
constraint rows and widens `b`, and `compactFactors` then drops unused factors
for free.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem ConPolyZono.compact_outer (C : ConPolyZono 𝕋 n) :
    C.construct ⊆ C.compact.construct :=
  subset_trans (ConPolyZono.compactGens_outer C)
    (subset_trans (ConPolyZono.compactCons_outer C.compactGens)
      (ConPolyZono.compactFactors_outer C.compactGens.compactCons))

end CORALean.Float
