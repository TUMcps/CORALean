module

public import CORALean.ContSet.Zonotope.Real.Theorems.MemWalkEdgesIff
public import CORALean.ContSet.Zonotope.Real.Theorems.CornerMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex

@[expose] public section

/-!
# The walk edges lie in the zonotope

An edge joins two sign corners, which are in the zonotope, and the zonotope is convex. It holds
for any order of the generators; the edges [1, Alg. 3] scans make up the boundary only once they
are sorted (`Zonotope.construct_eq_convexHull_walk`).

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the walk edges lie in `Z`

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.walkEdges_subset_construct (Z : Zonotope α) : -- --- CONCL ---
    Z.walkEdges ⊆ Z.construct := by -- --- PROOF ---
  -- an edge is a segment between two corners
  intro x hx
  obtain ⟨k, hk | hk⟩ := (Z.mem_walkEdges_iff x).mp hx
  · exact Z.convex_construct.segment_subset (Z.corner_mem_construct _) (Z.corner_mem_construct _) hk
  · exact Z.convex_construct.segment_subset (Z.corner_mem_construct _) (Z.corner_mem_construct _) hk

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
