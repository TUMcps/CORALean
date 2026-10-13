module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# CORA's `contSet/ne`: the negation of `isequal`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S α : Type} [ContSet S α] [Isequal S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `ne`: `res = ~isequal(S1, S2)`. -/
def ContSet.ne (s t : S) : Prop := ¬ Isequal.isequal s t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
