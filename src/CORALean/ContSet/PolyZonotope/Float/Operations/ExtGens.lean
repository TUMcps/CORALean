import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# The centre folded in as generator zero, over any ambient type

The family counterpart of `extG`, which lays the same generators out as the columns of a matrix
over `Vec`; this one is the exact layer's `Real.PolyZonotope.extG` read over stored floats, so a
set over matrices has it too.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre, then the dependent generators. -/
def PolyZonotope.extGens (pZ : PolyZonotope α) : Fin (pZ.h + 1) → α := Fin.cons pZ.c pZ.G

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
