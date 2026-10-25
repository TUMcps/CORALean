module

public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# A sign corner is the lowest corner plus the generators it flips

In coordinates, `corner s = corner (all -) + 2 ∑_{s j} g_j`: the walk of [1, Alg. 3] adds `2 g`
to the current vertex for each generator it passes.

## Inputs
* `Z` – planar zonotope
* `s` – corner signs
* `k` – coordinate

## Hypotheses
* none

## Conclusion
* the corner is the bottom plus twice the selected generators

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

theorem Zonotope.corner_eq_bottom (Z : Zonotope (Vec ℝ 2)) (s : Fin Z.h → Bool)
    (k : Fin 2) : -- --- CONCL ---
    Z.corner s k =
      Z.corner (fun _ => false) k + 2 * ∑ j, (if s j then Z.G j k else 0) := by -- --- PROOF ---
  rw [Zonotope.corner_apply, Zonotope.corner_apply, Finset.mul_sum, add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : s j
  · simp [h]; ring
  · simp [h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
