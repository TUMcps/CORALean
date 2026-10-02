import CORALean.ContSet.Polygon.Real.Operations.Empty

/-!
# `Polygon.empty` is the empty set
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.construct_empty :
    ContSet.construct Polygon.empty = (∅ : Set (Vec ℝ 2)) := by
  ext x
  simp [SetUnion.mem_construct, Polygon.empty]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
