import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Instances
import CORALean.ContSet.InflatedContSet.Theorems.IsCompact

/-!
# A float poly zonotope is compact

What this denotes is a nominal set plus an error box, so `InflatedContSet.isCompact_construct`
carries compactness across: the nominal set is compact as over ℝ, the box by
Heine–Borel.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.isCompact_construct (pZ : PolyZonotope (Vec 𝕋 n)) : IsCompact pZ.construct :=
  InflatedContSet.isCompact_construct pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
