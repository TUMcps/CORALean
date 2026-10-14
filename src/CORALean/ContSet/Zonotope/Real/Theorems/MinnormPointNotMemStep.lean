module

public import CORALean.ContSet.Zonotope.Real.Operations.MinnormPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.HRepEq
public import CORALean.ContSet.Zonotope.Real.Theorems.FacetNormalDotSelfPos
public import CORALean.ContSet.Zonotope.Real.Theorems.MinnormOffsetMulSqrt
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic

@[expose] public section

/-!
# `minnormPoint` is on the boundary

Stepping from the point further along the unit row of its facet leaves the zonotope: the facet's
inequality (the enclosing half of `hRep_eq` [1, Thm. 2]) is tight at the point. With
`minnormPoint_mem` this makes it a boundary point, and by `minnormPoint_dist` one at the
distance `minnorm Z`.

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

theorem Zonotope.minnormPoint_not_mem_step (Z : Zonotope (Vec ℝ (n + 1)))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) (S : Fin n → Fin Z.h)
    (hC : Z.facetNormal S ≠ 0) (t : ℝ) (ht : 0 < t) :
    Z.minnormPoint S +
      t • ((Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S))⁻¹ • Z.facetNormal S) ∉
      Z.construct := by -- --- PROOF ---
  have hCC := Zonotope.facetNormal_dotProduct_self_pos Z S hC
  have hs : 0 < Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) := Real.sqrt_pos.mpr hCC
  have hss : Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) ^ 2
      = Z.facetNormal S ⬝ᵥ Z.facetNormal S := Real.sq_sqrt hCC.le
  -- the facet inequality at the stepped point
  intro hmem
  rw [Zonotope.hRep_eq Z hspan] at hmem
  have h1 := hmem S
  unfold Zonotope.minnormPoint at h1
  have hdiff : Z.c + Z.minnormOffset S • ((Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S))⁻¹ •
      Z.facetNormal S) + t • ((Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S))⁻¹ •
      Z.facetNormal S) - Z.c = (Z.minnormOffset S + t) •
      ((Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S))⁻¹ • Z.facetNormal S) := by
    rw [add_smul]; abel
  rw [hdiff] at h1
  simp only [dotProduct_smul, smul_eq_mul] at h1
  -- it reads `(b + t) ‖C‖ ≤ Δd = b ‖C‖`, which `t > 0` contradicts
  have heq : (Z.minnormOffset S + t) * ((Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S))⁻¹ *
      (Z.facetNormal S ⬝ᵥ Z.facetNormal S)) = (Z.minnormOffset S + t) *
      Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) := by
    field_simp
    rw [hss]
  have hnn := Zonotope.minnormOffset_nonneg Z S
  rw [heq, abs_of_nonneg (mul_nonneg (by linarith) hs.le),
    ← Zonotope.minnormOffset_mul_sqrt Z S hC] at h1
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
