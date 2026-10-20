module

public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# The lowest corner is lowest

With every generator in the upper half-plane (`y ≥ 0`), the corner `c - ∑ g` has the least `y` of
the zonotope: the lowest vertex of [1, Alg. 3] and [1, Alg. 4] (lines 1-8).

## Inputs
* `Z` – planar zonotope
* `z` – point

## Hypotheses
* `hH` – generators point upward
* `hz` – `z` lies in `Z`

## Conclusion
* the bottom corner is the lowest point

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.corner_bottom_le (Z : Zonotope (Vec ℝ 2)) (hH : ∀ j, 0 ≤ Z.G j 1)
    {z : Vec ℝ 2} (hz : z ∈ Z.construct) : Z.corner (fun _ => false) 1 ≤ z 1 := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hz
  rw [Zonotope.comb_apply, Zonotope.corner_apply]
  have : ∑ j, (if (fun _ : Fin Z.h => false) j then (1 : ℝ) else -1) * Z.G j 1
      ≤ ∑ j, β j * Z.G j 1 := by
    refine Finset.sum_le_sum fun j _ => ?_
    have := abs_le.mp (hβ j)
    simp only [Bool.false_eq_true, if_false]
    nlinarith [hH j]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
