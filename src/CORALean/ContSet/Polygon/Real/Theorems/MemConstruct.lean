import CORALean.ContSet.Polygon.Real.Polygon

/-!
# Containment of a point in a polygon

CORA's `polygon/contains_` at a point: some piece contains it. Exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.mem_construct_iff (P : Polygon) (x : Vec ℝ 2) :
    x ∈ ContSet.construct P ↔ ∃ p ∈ P.sets, x ∈ VPolytope.construct p :=
  SetUnion.mem_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
