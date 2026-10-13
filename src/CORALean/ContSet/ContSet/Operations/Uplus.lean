import CORALean.ContSet.ContSet.ContSet


/-!
# CORA's `uplus`: the set itself

CORA's `uplus` is the identity, so it takes no operation class.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S α : Type} [ContSet S α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `uplus`: `S = S`. -/
def ContSet.uplus (s : S) : S := s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
