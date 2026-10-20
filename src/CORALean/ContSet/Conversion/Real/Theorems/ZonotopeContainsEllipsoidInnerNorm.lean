module

public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor

@[expose] public section

/-!
# A zonotope as an ellipsoid

## Inputs
* `Z` – zonotope
* `F` – transformation matrix
* `l` – squared ball radius

## Hypotheses
* `hF` – transformation invertible
* `hball` – ball around the transformed center lies in the zonotope

## Conclusion
* inner ellipsoid is contained in the zonotope

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3]: a ball of radius `√l` around the center of `F⁻¹ Z` puts `E(l F Fᵀ, z̄)` in
`Z`; `l ≤ ⌊F⁻¹ Z⌋²` is what that ball says. -/
theorem Zonotope.contains_ellipsoidInnerNorm (Z : Zonotope (Vec ℝ n)) (F : Mat ℝ n n) (l : ℝ)
    (hF : IsUnit F.det)
    (hball : ∀ x : Vec ℝ n, ‖x‖₂ ≤ √l → F⁻¹ *ᵥ Z.c + x ∈
      (⟨Z.h, F⁻¹ *ᵥ Z.c, fun j => F⁻¹ *ᵥ Z.G j⟩ : Zonotope (Vec ℝ n)).construct) : -- --- CONCL ---
    (Z.ellipsoidInnerNorm F l).construct ⊆ Z.construct := by -- --- PROOF ---
  rw [Zonotope.ellipsoidInnerNorm, Ellipsoid.construct_ofFactor]
  rintro _ ⟨u, hu, rfl⟩
  -- `√l u` is in the ball, so a point of `F⁻¹ Z`; map it back with `F`
  have hx : ‖√l • u‖₂ ≤ √l := by
    rw [norm₂_smul, abs_of_nonneg (Real.sqrt_nonneg l)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg l) hu
  obtain ⟨β, hβ, heq⟩ := hball _ hx
  refine ⟨β, hβ, ?_⟩
  have hmap := congrArg (F *ᵥ ·) heq
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv F hF, Matrix.one_mulVec] at hmap
  show Z.c + (√l • F) *ᵥ u = Z.c + ∑ j, β j • Z.G j
  rw [Matrix.smul_mulVec]
  exact hmap

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
