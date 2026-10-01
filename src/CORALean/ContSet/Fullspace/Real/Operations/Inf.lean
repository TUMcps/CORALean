import CORALean.ContSet.Fullspace.Real.Fullspace

/-!
# `Fullspace.Inf`

CORA's `fullspace.Inf(n)`: the full space in `n` dimensions, the only value of the type.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace.Inf(n)`. -/
def Fullspace.Inf (n : ℕ) : Fullspace n := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
