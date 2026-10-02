import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.VPolytope.Real.Instances
import CORALean.ContSet.InflatedContSet.Theorems.Convex

/-!
# A float vpolytope is convex

What this denotes is a nominal set plus an error box, so `InflatedContSet.convex_construct`
carries convexity across: the nominal set is convex as over ℝ, the box because
its coordinates are bounded independently.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.convex_construct (P : VPolytope 𝕋 n) : Convex ℝ P.construct :=
  InflatedContSet.convex_construct P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
