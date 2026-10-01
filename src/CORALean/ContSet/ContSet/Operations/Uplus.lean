import CORALean.ContSet.ContSet.ContSet


/-!
# CORA's `uplus`: the set itself

CORA's `uplus` is the identity, so it takes no operation class.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S α : Type} [ContSet S α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `uplus`: `S = S`. -/
def ContSet.uplus (s : S) : S := s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
