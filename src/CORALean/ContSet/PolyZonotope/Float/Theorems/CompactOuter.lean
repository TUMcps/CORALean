import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactFactorsOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactGensOuter

/-!
# `compact` over-approximates

`compactGens` merges columns and rounds; `compactFactors` then drops unused
factors for free.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.compact_outer (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.compact.construct :=
  subset_trans (PolyZonotope.compactGens_outer pZ)
    (PolyZonotope.compactFactors_outer pZ.compactGens)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
