module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# The centre folded in as generator zero

Split out of `QuadMap.lean` (issue #62): shared with `Mul.lean` in this
directory and with the float layer's own `quadMap` and `mul`, all outside
this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre as generator zero. -/
def PolyZonotope.extG (pZ : PolyZonotope α) : Fin (pZ.h + 1) → α := Fin.cons pZ.c pZ.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
