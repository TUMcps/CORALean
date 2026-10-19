module

public import CORALean.ContSet.EmptySet.Real.Operations.Vertices
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# `EmptySet.vertices` spans the empty set

The convex hull of no vertices is `∅`.

## Inputs
* `E` – empty set

## Hypotheses
* none

## Conclusion
* the convex hull of the vertices is the empty set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
