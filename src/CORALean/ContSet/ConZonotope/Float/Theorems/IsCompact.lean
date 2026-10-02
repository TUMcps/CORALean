import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.ConZonotope.Real.Instances
import CORALean.ContSet.InflatedContSet.Theorems.IsCompact

/-!
# A float con zonotope is compact

What this denotes is a nominal set plus an error box, so `InflatedContSet.isCompact_construct`
carries compactness across: the nominal set is compact as over ℝ, the box by
Heine–Borel.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.isCompact_construct (cZ : ConZonotope 𝕋 n) : IsCompact cZ.construct :=
  InflatedContSet.isCompact_construct cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
