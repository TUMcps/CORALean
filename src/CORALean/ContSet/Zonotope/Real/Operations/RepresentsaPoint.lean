module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.representsa_point`

CORA's `@zonotope/representsa_` at type `point` with tolerance `0`: no generator reaches anywhere,
`Gⱼ = 0` for every `j` (CORA: `nrGens == 0` after compacting zero generators).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/representsa_` at `point`. -/
def Zonotope.representsa_point (Z : Zonotope α) : Prop := ∀ j, Z.G j = 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
