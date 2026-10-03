import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# `EmptySet.isBounded`

CORA's `isBounded` of the emptyset, as the `Bool` it answers: always `true`: `∅` is compact, hence
bounded. Holds no scalar and computes nothing numeric; `EmptySet.isBounded_iff` says it is
boundedness of the set.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def EmptySet.isBounded (_ : EmptySet n) : Bool := true

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
