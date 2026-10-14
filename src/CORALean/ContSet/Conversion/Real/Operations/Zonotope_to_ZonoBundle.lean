module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

@[expose] public section

/-!
# A zonotope is a bundle of one — the construction

`Zonotope.zonoBundle` is the construction; `Zonotope_to_ZonoBundle` states and proves what it
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

def Zonotope.zonoBundle (Z : Zonotope α) : ZonoBundle α := ⟨1, fun _ => Z⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
