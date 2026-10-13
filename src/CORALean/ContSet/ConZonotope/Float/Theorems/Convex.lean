import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.ConZonotope.Real.Instances
import CORALean.ContSet.InflatedContSet.Theorems.Convex

/-!
# A float con zonotope is convex

What this denotes is a nominal set plus an error box, so `InflatedContSet.convex_construct`
carries convexity across: the nominal set is convex as over ℝ, the box because
its coordinates are bounded independently.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.convex_construct (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Convex ℝ cZ.construct :=
  InflatedContSet.convex_construct cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
