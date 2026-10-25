module

public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructSubsetWalk
public import CORALean.ContSet.Zonotope.Real.Theorems.CornerMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex

@[expose] public section

/-!
# A zonogon is the hull of its walk

For generators in the half-plane `y > 0 ∨ (y = 0 ∧ x ≥ 0)` sorted by angle, the `2 (h + 1)`
corners of `Zonotope.walk` have the zonogon as their convex hull: `construct_subset_walk` is the
inclusion of the zonogon in the hull, and the walk's corners are sign corners, hence in the
zonogon, which is convex. The walk is the vertex list [1, Alg. 3] scans (Sec. 3.2).

## Inputs
* `Z` – planar zonotope

## Hypotheses
* `h1` – generators point upward
* `h2` – generators sorted by angle

## Conclusion
* `Z` is the convex hull of the walk

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

theorem Zonotope.construct_eq_convexHull_walk (Z : Zonotope (Vec ℝ 2))
    (h1 : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0))
    (h2 : ∀ i j : Fin Z.h, i < j → 0 ≤ Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0) : -- --- CONCL ---
    Z.construct = convexHull ℝ (Set.range Z.walk) := by -- --- PROOF ---
  refine Set.Subset.antisymm (Z.construct_subset_walk h1 h2) (convexHull_min ?_ Z.convex_construct)
  rintro _ ⟨i, rfl⟩
  -- every walk corner is a sign corner
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [Zonotope.walk, Fin.append_left]
    exact Z.corner_mem_construct _
  · simp only [Zonotope.walk, Fin.append_right]
    exact Z.corner_mem_construct _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
