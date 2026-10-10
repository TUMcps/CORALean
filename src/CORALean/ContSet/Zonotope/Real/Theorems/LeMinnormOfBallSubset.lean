import CORALean.ContSet.Zonotope.Real.Theorems.ExistsMinnormFacet
import CORALean.ContSet.Zonotope.Real.Theorems.HRepEq
import CORALean.ContSet.Zonotope.Real.Theorems.ExistsMinnormFacet
import CORALean.ContSet.Zonotope.Real.Theorems.FacetNormalDotSelfPos
import CORALean.ContSet.Zonotope.Real.Theorems.MinnormOffsetMulSqrt

/-!
# No larger ball fits

A Euclidean ball around the centre inside the zonotope has radius at most `minnorm Z`: the ball
reaches the facet that attains the minimum, along its unit row, and the facet's inequality
(the enclosing half of `hRep_eq` [1, Thm. 2]) bounds the radius by that facet's offset.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.le_minnorm_of_ball_subset (Z : Zonotope (Vec ℝ (n + 1)))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) (r : ℝ) (hr : 0 ≤ r)
    (hball : ∀ y : Vec ℝ (n + 1), y ⬝ᵥ y ≤ r ^ 2 → Z.c + y ∈ Z.construct) :
    r ≤ Z.minnorm := by -- --- PROOF ---
  obtain ⟨S, hC, hoff⟩ := Zonotope.exists_minnormFacet Z hspan
  have hCC := Zonotope.facetNormal_dotProduct_self_pos Z S hC
  have hs : 0 < Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) := Real.sqrt_pos.mpr hCC
  have hss : Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) ^ 2
      = Z.facetNormal S ⬝ᵥ Z.facetNormal S := Real.sq_sqrt hCC.le
  -- the point of the ball along the unit row, at distance `r` from the centre
  set y : Vec ℝ (n + 1) := (r * (Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S))⁻¹) •
    Z.facetNormal S with hy
  have hyy : y ⬝ᵥ y ≤ r ^ 2 := by
    rw [hy, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    refine le_of_eq ?_
    field_simp
    rw [hss]
  -- the facet inequality at that point bounds `r` times the row length by the offset
  have hmem := hball y hyy
  rw [Zonotope.hRep_eq Z hspan] at hmem
  have h1 := hmem S
  rw [add_sub_cancel_left, hy, dotProduct_smul, smul_eq_mul] at h1
  have hCy : r * (Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S))⁻¹ *
      (Z.facetNormal S ⬝ᵥ Z.facetNormal S) =
      r * Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) := by
    field_simp
    rw [hss]
  rw [hCy, abs_of_nonneg (mul_nonneg hr hs.le), ← Zonotope.minnormOffset_mul_sqrt Z S hC] at h1
  rw [← hoff]
  exact le_of_mul_le_mul_right h1 hs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
