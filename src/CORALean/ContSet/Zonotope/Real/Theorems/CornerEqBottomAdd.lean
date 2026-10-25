module

public import CORALean.ContSet.Zonotope.Real.Theorems.CornerEqBottom
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# A sign corner as a vector: the lowest corner plus twice the flipped generators

`corner s = (c - ∑ g) + 2 ∑_{s j} g_j`, the vector form of `corner_eq_bottom`: the walk of
[1, Alg. 3] and [1, Alg. 4] starts at `P = c - ∑ g` (lines 1-8) and adds `2 g` per generator.

## Inputs
* `Z` – planar zonotope
* `s` – corner signs

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

theorem Zonotope.corner_eq_bottom_add (Z : Zonotope (Vec ℝ 2))
    (s : Fin Z.h → Bool) : -- --- CONCL ---
    Z.corner s =
      (Z.c - ∑ j, Z.G j) + (2 : ℝ) • ∑ j, (if s j then Z.G j else 0) := by -- --- PROOF ---
  ext k
  have hb : Z.corner (fun _ => false) k = Z.c k - ∑ j, Z.G j k := by
    rw [Zonotope.corner_apply]
    simp [sub_eq_add_neg, Finset.sum_neg_distrib]
  have hsum : (∑ j, if s j then Z.G j else 0) k = ∑ j, if s j then Z.G j k else 0 := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by by_cases h : s j <;> simp [h]
  rw [Zonotope.corner_eq_bottom, hb]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsum, Finset.sum_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
