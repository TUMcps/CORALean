module

public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaOrigin

@[expose] public section

/-!
# `ZonoBundle.representsa_origin`

CORA's `@zonoBundle/representsa_` for the type `'origin'`:
`representsa_(conZonotope(zB), 'origin')`, decided on the constrained zonotope of the bundle.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `representsa_(conZonotope(zB), 'origin')`. -/
def ZonoBundle.representsa_origin (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) : Prop :=
  (zB.conZonotopeAll hk).representsa_origin


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
