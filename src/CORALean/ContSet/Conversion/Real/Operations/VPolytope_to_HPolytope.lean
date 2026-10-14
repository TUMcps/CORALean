module

public import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# Vertices to halfspaces — the construction

`VPolytope.hPolytope` is the construction; `VPolytope_to_HPolytope` states and proves what it
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

noncomputable def VPolytope.hPolytope (P : VPolytope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    HPolytope α :=
  HPolytope.ofBounds Aq fun i => P.supportBound (Aq i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
