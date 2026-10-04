import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.splitIntoConvexSets`, over a floating-point scalar

The stored convex pieces, as over ℝ: a float polygon is a list of float convex polytopes, and
the list is returned as it is, so nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stored convex pieces. -/
def Polygon.splitIntoConvexSets (P : Polygon 𝕋) : List (VPolytope 𝕋 2) := P.sets

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
