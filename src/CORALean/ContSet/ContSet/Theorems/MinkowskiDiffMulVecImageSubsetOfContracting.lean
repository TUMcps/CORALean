module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffImageSubsetImageOfContracting
public import CORALean.Global.Tensor

@[expose] public section

/-!
# A perturbed matrix image, inner-approximated by a contraction

`minkowskiDiff_image_subset_image_of_contracting` at matrices: for an invertible `Ē`, a true `E`
with `‖Ē⁻¹ (E - Ē)‖ < 1` in the operator norm of the supremum norm, and a closed nonempty `X`, the
image `Ē X` minus any `B` covering `(Ē - E) X` lies inside `E X`. `P = Ē⁻¹` is the left inverse.

This is the statement for an interval matrix `[Ē ± R]` known to hold the true `e^{AΔt}`: the true
matrix is one fixed member `E`, and `‖Ē⁻¹ (E - Ē)‖` is at most `‖|Ē⁻¹| R‖`. A convex compact `X`
needs neither the bound nor `Ē` invertible (`minkowskiDiff_mulVec_image_subset_of_convex`).

## Inputs
* `Ē` – invertible matrix
* `E` – matrix
* `X` – domain set
* `B` – error set

## Hypotheses
* `hĒ` – `Ē` invertible
* `hK` – `‖Ē⁻¹ (E - Ē)‖ < 1`
* `hX` – `X` closed
* `hXne` – `X` nonempty
* `hB` – `B` covers `Ē x - E x` on `X`

## Conclusion
* `Ē X ⊖ B` lies in `E X`
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Ē X ⊖ B ⊆ E X` for an invertible `Ē` with `‖Ē⁻¹ (E - Ē)‖ < 1`, a closed nonempty `X`, and
`B` covering `Ē x - E x` on `X`. -/
theorem minkowskiDiff_mulVec_image_subset_of_contracting (Ē E : Mat ℝ n n) (hĒ : IsUnit Ē.det)
    (hK : ‖Ē⁻¹ * (E - Ē)‖ < 1) {X : Set (Vec ℝ n)} (hX : IsClosed X) (hXne : X.Nonempty)
    {B : Set (Vec ℝ n)} (hB : ∀ x ∈ X, Ē *ᵥ x - E *ᵥ x ∈ B) :
    minkowskiDiff ((Ē *ᵥ ·) '' X) B ⊆ (E *ᵥ ·) '' X := by -- --- PROOF ---
  -- `Ē⁻¹` undoes `Ē` on either side
  have hleft : ∀ x : Vec ℝ n, Ē⁻¹ *ᵥ (Ē *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hĒ, one_mulVec]
  have hinj : Function.Injective (Ē⁻¹.mulVecLin.toAddMonoidHom) := fun a b hab => by
    have h : Ē *ᵥ (Ē⁻¹ *ᵥ a) = Ē *ᵥ (Ē⁻¹ *ᵥ b) := congrArg (Ē *ᵥ ·) hab
    rwa [mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ hĒ, one_mulVec, one_mulVec] at h
  -- `x - Ē⁻¹ E x = -Ē⁻¹ (E - Ē) x`, Lipschitz with the operator norm
  have hg : ∀ x : Vec ℝ n, x - Ē⁻¹ *ᵥ (E *ᵥ x) = -((Ē⁻¹ * (E - Ē)) *ᵥ x) := fun x => by
    rw [Matrix.mul_sub, nonsing_inv_mul _ hĒ, sub_mulVec, one_mulVec, ← mulVec_mulVec, neg_sub]
  have hLip : LipschitzWith ‖Ē⁻¹ * (E - Ē)‖₊ fun x : Vec ℝ n => x - Ē⁻¹ *ᵥ (E *ᵥ x) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, hg, hg, neg_sub_neg, ← mulVec_sub, norm_sub_rev a b,
        coe_nnnorm]
      exact linfty_opNorm_mulVec _ _
  have hK' : ‖Ē⁻¹ * (E - Ē)‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    exact hK
  exact minkowskiDiff_image_subset_image_of_contracting (Ē⁻¹.mulVecLin.toAddMonoidHom) hinj
    (Ē *ᵥ ·) (E *ᵥ ·) hleft hK' hLip hX.isComplete hXne hB

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
