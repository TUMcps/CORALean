module

public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# How far a zonogon reaches from the lowest corner along a direction

A point of the zonotope is at most `∑ 2 max(σ g_x, 0)` beyond the lowest corner along `σ` in `x`:
the total reach of the generators pointing along `σ`. It is what makes the line meet the chain of
[1, Alg. 3] and [1, Alg. 4] when it meets the zonogon.

## Inputs
* `Z` – planar zonotope
* `σ` – direction sign
* `z` – point

## Hypotheses
* `hz` – `z` lies in `Z`

## Conclusion
* the reach of `z` along `σ` is at most the generator reach

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reach_le (Z : Zonotope (Vec ℝ 2)) (σ : ℝ) {z : Vec ℝ 2}
    (hz : z ∈ Z.construct) : -- --- CONCL ---
    σ * (z 0 - Z.corner (fun _ => false) 0) ≤ ∑ j, 2 * max (σ * Z.G j 0) 0 := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hz
  rw [Zonotope.comb_apply, Zonotope.corner_apply]
  have e1 : (Z.c 0 + ∑ j, β j * Z.G j 0) -
      (Z.c 0 + ∑ j, (if (fun _ : Fin Z.h => false) j then (1 : ℝ) else -1) * Z.G j 0)
      = ∑ j, (β j + 1) * Z.G j 0 := by
    simp only [Bool.false_eq_true, if_false]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have := abs_le.mp (hβ j)
  rcases le_total 0 (σ * Z.G j 0) with h | h
  · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right h]; nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
