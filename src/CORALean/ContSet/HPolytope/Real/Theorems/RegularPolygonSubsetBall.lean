module

public import CORALean.Global.ExistsRegularPolygonDotGe
public import CORALean.ContSet.HPolytope.Real.Operations.RegularPolygon
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# The regular polygon lies inside the disk

The polygon of `HPolytope.regularPolygon` approximates the Euclidean disk from inside. The disk is
written as `√(x₁² + x₂²) ≤ R`, since `Vec` carries the supremum norm.

## Inputs
* none

## Hypotheses
* `hN` – the polygon has at least three sides

## Conclusion
* every point of the polygon is at Euclidean distance at most `R` from the origin
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ} {R : ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.regularPolygon_subset_ball (hN : 3 ≤ N) : -- --- CONCL ---
    (HPolytope.regularPolygon N R).toSet ⊆
      {x : Vec ℝ 2 | √(x 0 ^ 2 + x 1 ^ 2) ≤ R} := by -- --- PROOF ---
  intro x hx
  rw [HPolytope.regularPolygon, HPolytope.mem_ineqs_iff] at hx
  -- the cosine of the half step is positive for three or more sides
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos (Real.pi / N) := by
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith [div_pos hpi (by linarith : (0 : ℝ) < N)], ?_⟩
    exact div_lt_div_of_pos_left hpi two_pos (by linarith)
  -- a direction of the polygon within half a step of `x`
  obtain ⟨k, hk⟩ := exists_regularPolygon_dot_ge (by omega : 0 < N) (x 0) (x 1)
  have hrow := hx k
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hrow
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hrow
  exact le_of_mul_le_mul_right (by linarith) hcos

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
