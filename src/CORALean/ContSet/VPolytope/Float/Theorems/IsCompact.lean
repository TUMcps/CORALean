import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.VPolytope.Real.Instances
import CORALean.ContSet.InflatedContSet.Theorems.IsCompact

/-!
# A float vpolytope is compact

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

theorem VPolytope.isCompact_construct (P : VPolytope 𝕋 n) : IsCompact P.construct :=
  InflatedContSet.isCompact_construct P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
