import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Theorems.Convex

/-!
# A float zonotope bundle is convex

An intersection of convex sets, `convex_iInter` over the members' own
convexity — which at this layer already covers each member's error box, the
box being inside what a member denotes. Holds vacuously at `k = 0`, `univ`
being convex too.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.convex_construct (zB : ZonoBundle (Vec 𝕋 n)) : Convex ℝ zB.construct :=
  convex_iInter fun i => Zonotope.convex_construct (zB.Z i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
