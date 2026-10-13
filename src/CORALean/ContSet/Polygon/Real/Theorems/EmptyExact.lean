module

public import CORALean.ContSet.Polygon.Real.Operations.Empty
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# `Polygon.empty` is the empty set
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.construct_empty :
    ContSet.construct Polygon.empty = (∅ : Set (Vec ℝ 2)) := by
  ext x
  simp [SetUnion.mem_construct, Polygon.empty]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
