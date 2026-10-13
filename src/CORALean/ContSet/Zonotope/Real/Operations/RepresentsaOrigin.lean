module

public import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaPoint

@[expose] public section

/-!
# `Zonotope.representsa_origin`

CORA's `@zonotope/representsa_` at type `origin` with tolerance `0`: a point at `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/representsa_` at `origin`. -/
def Zonotope.representsa_origin (Z : Zonotope α) : Prop := Z.c = 0 ∧ Z.representsa_point

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
