import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaPoint

/-!
# `Zonotope.representsa_origin`

CORA's `@zonotope/representsa_` at type `origin` with tolerance `0`: a point at `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/representsa_` at `origin`. -/
def Zonotope.representsa_origin (Z : Zonotope α) : Prop := Z.c = 0 ∧ Z.representsa_point

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
