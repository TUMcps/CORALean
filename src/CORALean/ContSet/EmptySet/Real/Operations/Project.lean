import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# `EmptySet.project`

CORA's `@emptySet/project`: only the dimension changes, to the number of kept coordinates.
`dims` lists the kept coordinates, as in CORA, and `Fin m → Fin n` is its range check.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/project`. -/
def EmptySet.project (_ : EmptySet n) (_ : Fin m → Fin n) : EmptySet m := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
