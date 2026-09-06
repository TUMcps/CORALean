import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactFactorsOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactGensOuter

/-!
# `compact` over-approximates

`compactGens` merges columns and rounds; `compactFactors` then drops unused
factors for free.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.compact_outer (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ PZ.compact.construct :=
  subset_trans (PolyZonotope.compactGens_outer PZ)
    (PolyZonotope.compactFactors_outer PZ.compactGens)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
