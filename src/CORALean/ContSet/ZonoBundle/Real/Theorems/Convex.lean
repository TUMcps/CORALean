import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Zonotope.Real.Theorems.Convex

/-!
# A zonotope bundle is convex

An intersection of convex sets, `convex_iInter` applied to each component's own
convexity — which holds vacuously at `k = 0`, `univ` being convex too.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.convex_construct (B : ZonoBundle α) : Convex ℝ B.construct :=
  convex_iInter fun i => (B.Z i).convex_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
