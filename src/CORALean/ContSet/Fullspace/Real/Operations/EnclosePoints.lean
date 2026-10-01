import CORALean.ContSet.Fullspace.Real.Fullspace

/-!
# `Fullspace.enclosePoints`

CORA's `@fullspace/enclosePoints`: `fullspace(size(points,1))`, the full space of the points'
dimension.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/enclosePoints`: the points are the columns of `points`. -/
def Fullspace.enclosePoints {p : ℕ} (_ : Fin p → Vec ℝ n) : Fullspace n := ⟨⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
