import CORALean.ContSet.Fullspace.Real.Fullspace

/-!
# `Fullspace.isBounded`

CORA's `isBounded` of the fullspace, as the `Bool` it answers: `dim(fs) == 0`: `false` in every
positive dimension. Holds no scalar and computes nothing numeric; `Fullspace.isBounded_iff` says
it is boundedness of the set.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Fullspace.isBounded (_ : Fullspace n) : Bool := decide (n = 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
