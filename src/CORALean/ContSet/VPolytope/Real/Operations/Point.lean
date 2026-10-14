module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# `VPolytope.point`

One vertex, which is the singleton. Composed with `plus` this is a translation,
so the representation needs no separate one.

One vertex, which is the singleton.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.point (v : α) : VPolytope α := ⟨1, fun _ => v⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
