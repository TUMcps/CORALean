module

public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# A zonotope as halfspaces — the construction

`Zonotope.hPolytope` is the construction; `Zonotope_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.hPolytope (Z : Zonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  HPolytope.ofBounds Aq fun i => Z.supportBound (Aq i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
