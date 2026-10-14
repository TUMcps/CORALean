module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

@[expose] public section

/-!
# One component of a bundle, enclosing it — the construction

`ZonoBundle.zonotope` is the construction; `ZonoBundle_to_Zonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.zonotope (zB : ZonoBundle α) (i : Fin zB.k) : Zonotope α := zB.Z i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
