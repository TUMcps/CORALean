import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# The centre folded in as generator zero

Split out of `QuadMap.lean` (issue #62): shared with `Mul.lean` in this
directory and with the float layer's own `quadMap` and `mul`, all outside
this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre as generator zero. -/
def PolyZonotope.extG (S : PolyZonotope α) : Fin (S.h + 1) → α := Fin.cons S.c S.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
