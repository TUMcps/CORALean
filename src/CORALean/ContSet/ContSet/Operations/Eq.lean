import CORALean.ContSet.ContSet.ContSet

/-!
# CORA's `contSet/eq`: an alias of `isequal`
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S α : Type} [ContSet S α] [Isequal S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `eq`: `res = isequal(S1, S2)`. -/
def ContSet.eq (s t : S) : Prop := Isequal.isequal s t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
