module

public import CORALean.ContSet.ZonoBundle.Real.Operations.RepresentsaOrigin
public import CORALean.ContSet.ConZonotope.Real.Theorems.RepresentsaOriginIff

@[expose] public section

/-!
# The bundle is the origin exactly when its constrained zonotope is

`conZonotopeAll` denotes the bundle (`conZonotopeAll_exact`), so what a constrained zonotope's
`representsa_origin` decides, exactly (`representsa_origin_iff`), it decides for the bundle.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.representsa_origin_iff (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    zB.construct = {0} ↔ zB.representsa_origin hk := by
  rw [← ZonoBundle.conZonotopeAll_exact zB hk]
  exact ConZonotope.representsa_origin_iff _


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
