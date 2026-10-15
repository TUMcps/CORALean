module

public import CORALean.ContSet.HPolytope.Real.Operations.RowLin

@[expose] public section

/-!
# `HPolytope.eqs`

CORA's `polytope([], [], Ae, be)`: one equality per row.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `polytope([], [], Ae, be)`: one equality per row. -/
def HPolytope.eqs (Ae : Mat ℝ q n) (be : Vec ℝ q) : HPolytope (Vec ℝ n) where
  m := 0
  A := Fin.elim0
  b := Fin.elim0
  me := q
  Ae := HPolytope.rowLin Ae
  be := be

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
