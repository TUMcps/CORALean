module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex

@[expose] public section

/-!
# A zonotope bundle is convex

An intersection of convex sets, `convex_iInter` applied to each component's own
convexity — which holds vacuously at `k = 0`, `univ` being convex too.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.convex_construct (zB : ZonoBundle α) : Convex ℝ zB.construct :=
  convex_iInter fun i => (zB.Z i).convex_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
