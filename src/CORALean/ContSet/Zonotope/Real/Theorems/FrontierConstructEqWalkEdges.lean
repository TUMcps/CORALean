module

public import CORALean.ContSet.Zonotope.Real.Theorems.FrontierSubsetWalkEdges
public import CORALean.ContSet.Zonotope.Real.Theorems.WalkEdgesSubsetFrontier

@[expose] public section

/-!
# The boundary of a zonogon is the union of the walk edges

For generators in the half-plane `y > 0 ∨ (y = 0 ∧ x ≥ 0)` sorted by angle, nonzero, and at least
one of them, `frontier Z.construct = Z.walkEdges`: the segments `[P; P + 2g]` of the first block of
the walk (the chain up one side, increasing angle) and of the second (back down the other) are the
boundary, [1, Alg. 3]. `frontier_subset_walkEdges` needs neither nonzero generators nor
more than the order; a zero generator only adds a degenerate edge, a point, to the right-hand side,
which is on the boundary too but is not covered by a line.

## Inputs
* `Z` – planar zonotope

## Hypotheses
* `hh` – at least one generator
* `h1` – generators point upward
* `h2` – generators sorted by angle
* `hne` – generators nonzero

## Conclusion
* the frontier equals the walk edges

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems Reachability
      Analysis". Hybrid Systems: Computation and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.frontier_construct_eq_walkEdges (Z : Zonotope (Vec ℝ 2)) (hh : 0 < Z.h)
    (h1 : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0))
    (h2 : ∀ i j : Fin Z.h, i < j → 0 ≤ Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0)
    (hne : ∀ j, Z.G j ≠ 0) : frontier Z.construct = Z.walkEdges :=
  Set.Subset.antisymm (Z.frontier_subset_walkEdges hh h1 h2) (Z.walkEdges_subset_frontier h2 hne)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
