module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.recenter`

CORA's `zonotope` with `c` zeroed: the same generators, moved to hold the
origin instead of the center. What `Recenter` asks a representation with a
center to supply, alongside `Zonotope.c` itself as `center`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The zonotope moved to the origin, keeping its generators. -/
def Zonotope.recenter (Z : Zonotope α) : Zonotope α := ⟨Z.h, 0, Z.G⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
