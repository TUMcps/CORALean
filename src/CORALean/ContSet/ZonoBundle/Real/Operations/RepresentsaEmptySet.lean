module

public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaEmptySet

@[expose] public section

/-!
# `ZonoBundle.representsa_emptySet`

CORA's `@zonoBundle/representsa_` for the type `'emptySet'`: `representsa_(conZonotope(zB),
'emptySet')`. (`aux_emptySet` also answers `true` for no members and when some member is empty; no
`Zonotope` is empty, and a bundle of no members denotes the whole space here, so both shortcuts are
outside `0 < k`.)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `representsa_(conZonotope(zB), 'emptySet')`. -/
def ZonoBundle.representsa_emptySet (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) : Prop :=
  (zB.conZonotopeAll hk).representsa_emptySet


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
