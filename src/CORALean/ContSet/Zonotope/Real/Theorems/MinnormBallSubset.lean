module

public import CORALean.ContSet.Zonotope.Real.Operations.Minnorm
public import CORALean.ContSet.Zonotope.Real.Theorems.HRepEq
public import CORALean.ContSet.Zonotope.Real.Theorems.FacetNormalDotSelfPos
public import CORALean.ContSet.Zonotope.Real.Theorems.MinnormOffsetMulSqrt
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic

@[expose] public section

/-!
# The `minnorm` ball lies in the zonotope

For a zonotope whose generators span the space, the Euclidean ball around the center of radius
`minnorm Z` is inside `Z`: every point of it satisfies each facet inequality, by Cauchy-Schwarz
against the unit row, and the facet inequalities are the zonotope (`hRep_eq` [1, Thm. 2]).

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minnorm_ball_subset (Z : Zonotope (Vec ℝ (n + 1)))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) (y : Vec ℝ (n + 1))
    (hy : y ⬝ᵥ y ≤ Z.minnorm ^ 2) : Z.c + y ∈ Z.construct := by -- --- PROOF ---
  have hnn : 0 ≤ Z.minnorm := Real.sInf_nonneg (by
    rintro _ ⟨S, -, rfl⟩
    exact Zonotope.minnormOffset_nonneg Z S)
  rw [Zonotope.hRep_eq Z hspan]
  intro S
  rw [add_sub_cancel_left]
  by_cases hC : Z.facetNormal S = 0
  · simp [hC]
  -- the unit row: `|C·y| ≤ ‖C‖‖y‖ ≤ ‖C‖ · minnorm ≤ ‖C‖ · b_S = Δd`
  have hCC := Zonotope.facetNormal_dotProduct_self_pos Z S hC
  have hs : 0 < Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) := Real.sqrt_pos.mpr hCC
  have hle : Z.minnorm ≤ Z.minnormOffset S :=
    csInf_le ⟨0, by
      rintro _ ⟨S', -, rfl⟩
      exact Zonotope.minnormOffset_nonneg Z S'⟩ ⟨S, hC, rfl⟩
  -- Cauchy-Schwarz, then the radius bound on `y`
  have hsq : (Z.facetNormal S ⬝ᵥ y) ^ 2 ≤ (Z.facetNormal S ⬝ᵥ Z.facetNormal S) * (y ⬝ᵥ y) := by
    simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (Z.facetNormal S) y
  have habs : |Z.facetNormal S ⬝ᵥ y|
      ≤ Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) * Z.minnorm := by
    refine abs_le_of_sq_le_sq ?_ (mul_nonneg hs.le hnn)
    rw [mul_pow, Real.sq_sqrt hCC.le]
    exact hsq.trans (mul_le_mul_of_nonneg_left hy hCC.le)
  calc |Z.facetNormal S ⬝ᵥ y|
      ≤ Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) * Z.minnorm := habs
    _ ≤ Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) * Z.minnormOffset S :=
        mul_le_mul_of_nonneg_left hle hs.le
    _ = ∑ υ, |Z.facetNormal S ⬝ᵥ Z.G υ| := by
        rw [mul_comm]; exact Zonotope.minnormOffset_mul_sqrt Z S hC

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
