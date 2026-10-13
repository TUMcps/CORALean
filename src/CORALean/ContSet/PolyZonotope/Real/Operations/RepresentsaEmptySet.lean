import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.representsa_emptySet`

CORA's `@polyZonotope/representsa_` at type `emptySet`: `false`. A polynomial zonotope cannot denote
the empty set (the factor vector `0` is always allowed), which `representsa_emptySet_iff` states.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polyZonotope/representsa_` at `emptySet`. -/
def PolyZonotope.representsa_emptySet (_pZ : PolyZonotope α) : Bool := false

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
