import CORALean.ContSet.EmptySet.Real.Operations.Vertices
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.vertices` spans the empty set

The convex hull of no vertices is `∅`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.vertices_exact (E : EmptySet n) :
    convexHull ℝ (Set.range E.vertices) = construct E := by
  have h : Set.range E.vertices = ∅ := Set.range_eq_empty _
  rw [h]
  exact convexHull_empty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
