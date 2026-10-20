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
* `r` – bound on the squared norm

## Hypotheses
* `hF` – transformation invertible
* `hr` – bound covers the squared maximal norm

## Conclusion
* zonotope is contained in its ellipsoid

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

/-- [1, Thm. 1]: `r` bounding `⌈F⁻¹ Z⌉²` makes `E(r F Fᵀ, z̄)` enclose `Z`. -/
theorem Zonotope.ellipsoidNorm_contains (Z : Zonotope (Vec ℝ n)) (F : Mat ℝ n n) (r : ℝ)
    (hF : IsUnit F.det)
    (hr : (⟨Z.h, F⁻¹ *ᵥ Z.c, fun j => F⁻¹ *ᵥ Z.G j⟩ : Zonotope (Vec ℝ n)).maxNormSq ≤ r) :
    Z.construct ⊆ (Z.ellipsoidNorm F r).construct := by -- --- PROOF ---
  rw [Zonotope.ellipsoidNorm, Ellipsoid.construct_ofFactor]
  rintro _ ⟨β, hβ, rfl⟩
  -- the transformed point `v = F⁻¹ ∑ βⱼ gⱼ` is no longer than `√r`
  set v : Vec ℝ n := ∑ j, β j • (F⁻¹ *ᵥ Z.G j) with hv
  have hvle : ‖v‖₂ ^ 2 ≤ r :=
    le_trans (Zonotope.sq_norm₂_le_maxNormSq ⟨Z.h, F⁻¹ *ᵥ Z.c, fun j => F⁻¹ *ᵥ Z.G j⟩ hβ) hr
  have hFv : F *ᵥ v = ∑ j, β j • Z.G j := by
    simp only [hv, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv F hF, Matrix.one_mulVec]
  have hr0 : 0 ≤ r := le_trans (sq_nonneg _) hvle
  rcases hr0.eq_or_lt with hr0 | hrpos
  -- `r = 0`: the point is the center
  · subst hr0
    have hv0 : v = 0 := by
      rw [← dotProduct_self_eq_zero, dotProduct_self]
      nlinarith [norm₂_nonneg v]
    refine ⟨0, by rw [norm₂_zero]; exact zero_le_one, ?_⟩
    rw [Matrix.mulVec_zero, ← hFv, hv0, Matrix.mulVec_zero]
  -- otherwise `u = v / √r` is in the unit ball and `√r F u = F v`
  · have hs : 0 < √r := Real.sqrt_pos.mpr hrpos
    refine ⟨(√r)⁻¹ • v, ?_, ?_⟩
    · show ‖((√r)⁻¹ • v : Vec ℝ n)‖₂ ≤ 1
      rw [norm₂_smul, abs_of_pos (inv_pos.mpr hs), inv_mul_le_iff₀ hs, mul_one]
      calc ‖v‖₂ = √(‖v‖₂ ^ 2) := (Real.sqrt_sq (norm₂_nonneg v)).symm
        _ ≤ √r := Real.sqrt_le_sqrt hvle
    · show Z.c + ∑ j, β j • Z.G j = Z.c + (√r • F) *ᵥ ((√r)⁻¹ • v)
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hs.ne', one_smul,
        hFv]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
