import CORALean.ContSet.Fullspace.Real.Fullspace

/-!
# `Fullspace.projectHighDim_`

CORA's `@fullspace/projectHighDim_`: the object itself when `proj` has `N` entries, an
error otherwise (a new dimension would have to be held at `0`, which the full space cannot
say). Total here; the guarantee is stated for `n = N`, the one case CORA answers.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/projectHighDim_`. -/
def Fullspace.projectHighDim_ (_ : Fullspace n) (N : ℕ) (_ : Fin n → Fin N) : Fullspace N := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
