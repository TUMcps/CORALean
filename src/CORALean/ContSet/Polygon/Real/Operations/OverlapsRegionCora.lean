module

public import CORALean.ContSet.Polygon.Real.Polygon

@[expose] public section

/-!
# `@polygon/isIntersecting_.m` l. 52 on regions

`overlaps(pgon.set, S.set)`, here: the regions of the two polyshapes share a point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `overlaps(P, S')`. -/
def Polygon.overlapsRegionCora (P S' : Set (Vec ℝ 2)) : Prop := (P ∩ S').Nonempty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
