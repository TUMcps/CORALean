import CORALean.ContSet.HPolytope.Real.Operations.RowLin

/-!
# `HPolytope.eqs`

CORA's `polytope([], [], Ae, be)`: one equality per row.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {q n : ℕ}

/-- CORA's `polytope([], [], Ae, be)`: one equality per row. -/
def HPolytope.eqs (Ae : Mat ℝ q n) (be : Vec ℝ q) : HPolytope (Vec ℝ n) where
  m := 0
  A := Fin.elim0
  b := Fin.elim0
  me := q
  Ae := HPolytope.rowLin Ae
  be := be

end CORALean.Real
