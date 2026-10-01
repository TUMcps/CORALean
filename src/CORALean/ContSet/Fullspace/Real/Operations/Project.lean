import CORALean.ContSet.Fullspace.Real.Fullspace

/-!
# `Fullspace.project`

CORA's `@fullspace/project`: only the dimension changes, to the number of kept
coordinates. CORA throws at `n = 0`; nothing here does.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/project`. -/
def Fullspace.project (_ : Fullspace n) (_ : Fin m → Fin n) : Fullspace m := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
